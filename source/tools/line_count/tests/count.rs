mod common;
use common::*;

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
    insta::assert_snapshot!(line_count_file_print_all("full.rs"), @r"
    Category           | Detailed contents              |

    # full.rs
    Comment            | Comment                        | //! This test tries to use most of the verus syntax to test the line_counter
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | verus! {
                       |                                |
    Comment            | Comment                        | /// How a dog barks
                       | Trait                          | pub trait Barker {
    Definitions        | TypeDefinition Trait           |     type Env;
                       | Trait                          |
    Comment            | Comment                        |     /// Whether bark obeys the spec (should be deterministic wrt the environment)
    Spec               | Trait Signature(Spec           |     spec fn obeys_bark_spec() -> bool;
                       | Trait                          |
    Comment            | Comment                        |     /// Specification of bark
    Spec               | Trait Signature(Spec           |     spec fn spec_bark(self, env: Self::Env) -> u64;
                       | Trait                          |
    Comment            | Comment                        |     /// Preconditions on bark
    Spec               | Trait Signature(Spec           |     spec fn bark_pre(self, env: Self::Env) -> bool;
                       | Trait                          |
    Comment            | Comment                        |     /// Returns the loudness of the bark
    Exec               | Trait Signature(Exec           |     fn bark(&self, env: &Self::Env) -> (r: u64)
    Spec               | Trait Signature FunctionS      |         requires
    Exec               | Code(E Trait Signat Functi     |             self.bark_pre(*env),
    Spec               | Trait Signature FunctionS      |         ensures
    Exec               | Code(E Trait Signat Functi     |             Self::obeys_bark_spec() ==> r == self.spec_bark(*env),
                       | Trait                          |         ;
                       | Trait                          | }
                       |                                |
                       | Impl                           | impl Barker for u64 {
                       | Impl                           |     type Env = ();
                       | Impl                           |
    Spec               | Code(S Impl Signat Body(S      |     open spec fn obeys_bark_spec() -> bool {
    Spec               | Code(Spec Impl Body(Spec       |         true
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           |
    Spec               | Code(S Impl Signat Body(S      |     open spec fn spec_bark(self, env: Self::Env) -> u64 {
    Spec               | Code(Spec Impl Body(Spec       |         self
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           |
    Spec               | Code(S Impl Signat Body(S      |     open spec fn bark_pre(self, env: Self::Env) -> bool {
    Spec               | Code(Spec Impl Body(Spec       |         true
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           |
    Exec               | Code(E Impl Signat Body(E      |     fn bark(&self, env: &Self::Env) -> u64 {
    Exec               | Code(Exec Impl Body(Exec       |         *self
    Exec               | Code(Exec Impl Body(Exec       |     }
                       | Impl                           | }
                       |                                |
    Exec Directives    | DatatypeDecl Directive         | #[derive(PartialEq, Eq)]
    Exec               | DatatypeDecl                   | pub struct Dog<B: Barker> {
    Exec               | DatatypeDecl                   |     pub fur: bool,
    Exec               | DatatypeDecl                   |     pub barker: B,
    Exec               | DatatypeDecl                   | }
                       |                                |
    Exec Directives    | DatatypeDecl Directive         | #[derive(PartialEq, Eq)]
    Exec               | DatatypeDecl                   | pub enum Animal {
    Exec               | DatatypeDecl                   |     Dog(Dog<u64>),
    Exec               | DatatypeDecl                   |     Cat(bool),
    Exec               | DatatypeDecl                   |     Mouse,
    Exec               | DatatypeDecl                   | }
                       |                                |
                       | Impl                           | impl Animal {
    Exec               | Impl Signature(Exec            |     pub fn bark(&self) -> (r: u64)
    Spec               | Impl Signature FunctionS       |         ensures
    Spec               | Impl Signature FunctionS       |             r == self.spec_bark()
    Exec               | Code(Exec Impl Body(Exec       |     {
    Exec               | Code(Exec Impl Body(Exec       |         match self {
    Exec               | Code(Exec Impl Body(Exec       |             Animal::Dog(d) => d.barker.bark(&()),
    Exec               | Code(Exec Impl Body(Exec       |             _ => 0
    Exec               | Code(Exec Impl Body(Exec       |         }
    Exec               | Code(Exec Impl Body(Exec       |     }
                       | Impl                           |
    Spec               | Code(S Impl Signat Body(S      |     pub open spec fn spec_bark(self) -> u64 {
    Spec               | Code(Spec Impl Body(Spec       |         match self {
    Spec               | Code(Spec Impl Body(Spec       |             Animal::Dog(d) => d.barker.spec_bark(()),
    Spec               | Code(Spec Impl Body(Spec       |             _ => 0
    Spec               | Code(Spec Impl Body(Spec       |         }
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           | }
                       |                                |
    Exec               | Code(Exec Signature Body(Exec  | fn test_struct_1(p: u64) {
    Exec               | Code(Exec) Body(Exec)          |     let c1 = Dog { fur: true, barker: p };
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(c1.barker == p);
    Proof              | Code(Exec ProofDire Body(Exec  |     assert((Dog { barker: p, fur: true }).barker == p);
    Exec               | Code(Exec) Body(Exec)          |     let bark = (Dog { barker: p, fur: true }).barker.bark(&());
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(bark == p);
    Proof              | Code(Exec ProofDire Body(Exec  |     assert((Dog { barker: p, fur: true }).barker.spec_bark(()) == p);
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Exec               | Code(Exec Signature Body(Exec  | fn test_structural_eq(barker: u64) {
    Exec               | Code(Exec) Body(Exec)          |     let d1 = Dog { barker, fur: true };
    Exec               | Code(Exec) Body(Exec)          |     let d2 = Dog { barker, fur: false };
    Exec               | Code(Exec) Body(Exec)          |     let d3 = Dog { barker, fur: true };
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(d1 == d3);
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(d1 != d2);
    Exec               | Code(Exec) Body(Exec)          |     let cat = Animal::Cat(true);
    Exec               | Code(Exec) Body(Exec)          |     let dog = Animal::Dog(d1);
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(cat != dog);
    Exec               | Code(Exec) Body(Exec)          |     let cat_bark = cat.bark();
    Exec               | Code(Exec) Body(Exec)          |     let dog_bark = dog.bark();
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(cat_bark == 0);
    Proof              | Code(Exec ProofDire Body(Exec  |     assert(dog_bark == barker);
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // Cats don't bark
    Proof              | Signature(Proof)               | proof fn equal_bark_means_dog_mute(dog: Animal, cat: Animal)
    Spec               | Signature(Proo FunctionSpec    |     requires
    Spec               | Signature(Proo FunctionSpec    |         dog is Dog,
    Spec               | Signature(Proo FunctionSpec    |         cat is Cat,
    Spec               | Signature(Proo FunctionSpec    |     ensures
    Spec               | Signature(Proo FunctionSpec    |         dog.spec_bark() == cat.spec_bark() ==> dog->Dog_0.barker == 0
    Proof              | Code(Proof) Body(Proof)        | {
    Trusted            | Code(Proo Assumptio Body(Proo  |     admit();
    Proof              | Code(Proof) Body(Proof)        | }
                       |                                |
    Spec               | Code(Spec Signature Body(Spec  | spec fn sum_3_barks<B: Barker>(b: B, env: B::Env) -> int {
    Spec               | Code(Spec) Body(Spec)          |     b.spec_bark(env) + b.spec_bark(env) + b.spec_bark(env)
    Spec               | Code(Spec) Body(Spec)          | }
                       |                                |
    Proof              | Signature(Proof)               | pub broadcast axiom fn dog_louder_than_cat(cat: Animal, dog: Animal)
    Spec               | Signature(Proo FunctionSpec    |     requires
    Spec               | Signature(Proo FunctionSpec    |         cat is Cat,
    Spec               | Signature(Proo FunctionSpec    |         dog is Dog,
    Spec               | Signature(Proo FunctionSpec    |     ensures
    Spec               | Signature(Proo FunctionSpec    |         #[trigger] dog.spec_bark() >= #[trigger] cat.spec_bark()
    Proof              | Code(Proof) Body(Proof)        | ;
                       |                                |
    Exec               | Code(Exec Signature Body(Exec  | fn main() {}
                       |                                |
                       |                                | } // verus!

    | file    | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted | Definitions |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | full.rs |       1 |   35 |    14 |   38 |          0 |       7 |      0 |          33 | 1           |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | total   |       1 |   35 |    14 |   38 |          0 |       7 |      0 |          33 | 1           |
    ");
}

#[test]
fn test_line_count_spec_fn() {
    insta::assert_snapshot!(line_count_file_print_all("spec_fn.rs"), @r"
    Category           | Detailed contents              |

    # spec_fn.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | verus! {
                       |                                |
    Spec               | Code(Spec Signature Body(Spec  | spec fn min(x: int, y: int) -> int {
    Spec               | Code(Spec) Body(Spec)          |     if x <= y {
    Spec               | Code(Spec) Body(Spec)          |         x
    Spec               | Code(Spec) Body(Spec)          |     } else {
    Spec               | Code(Spec) Body(Spec)          |         y
    Spec               | Code(Spec) Body(Spec)          |     }
    Spec               | Code(Spec) Body(Spec)          | }
                       |                                |
                       |                                | }

    | file       | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | spec_fn.rs |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total      |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    ");
}

#[test]
fn test_line_count_no_verus() {
    insta::assert_snapshot!(line_count_file_print_all("no_verus.rs"), @r"
    Category           | Detailed contents              |

    # no_verus.rs
                       |                                | fn exec_min(a: u32, b: u32) -> u32 {
                       |                                |     if a < b { a } else { b }
                       |                                | }

    | file        | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | no_verus.rs |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total       |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    ");
}

#[test]
fn test_line_verus_outside() {
    insta::assert_snapshot!(line_count_file_print_all("verus_outside.rs"), @r"
    Category           | Detailed contents              |

    # verus_outside.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | fn exec_min(a: u32, b: u32) -> u32 {
                       |                                |     if a < b { a } else { b }
                       |                                | }
                       |                                |
                       |                                | verus! {
                       |                                |
    Spec               | Code(Spec Signature Body(Spec  | spec fn spec_min(a: u32, b: u32) -> u32 {
    Spec               | Code(Spec) Body(Spec)          |     if a < b { a } else { b }
    Spec               | Code(Spec) Body(Spec)          | }
                       |                                |
    Trusted            | FunctionSpec                   | assume_specification[exec_min](a: u32, b: u32) -> (r: u32)
    Trusted            | FunctionSpec                   |     ensures
    Trusted            | FunctionSpec                   |         r == spec_min(a, b)
    Trusted            | FunctionSpec                   | ;
                       |                                |
                       |                                | }

    | file             | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_outside.rs |       4 |    3 |     0 |    0 | 0          | 0       | 0      | 11          |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total            |       4 |    3 |     0 |    0 | 0          | 0       | 0      | 11          |
    ");
}

#[test]
fn test_line_verus_verify() {
    insta::assert_snapshot!(line_count_file_print_all("verus_verify.rs"), @r"
    Category           | Detailed contents              |

    # verus_verify.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | #[verus_verify]
    Exec               | Code(Exec Signature Body(Exec  | pub fn identity(value: u64) -> u64 {
    Exec               | Code(Exec) Body(Exec)          |     value
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
                       |                                | fn main() {}

    | file            | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-----------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_verify.rs |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    |-----------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total           |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    ");
}

#[test]
fn test_line_verus_verify_dual_spec() {
    insta::assert_snapshot!(line_count_file_print_all("verus_verify_dual_spec.rs"), @r"
    Category           | Detailed contents              |

    # verus_verify_dual_spec.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | #[verus_verify(dual_spec)]
    Exec               | Code(Exec Signature Body(Exec  | pub fn identity(value: u64) -> u64 {
    Exec               | Code(Exec) Body(Exec)          |     value
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
                       |                                | fn main() {}

    | file                      | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |---------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_verify_dual_spec.rs |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    |---------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total                     |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    ");
}

#[test]
fn test_multiple_item_attributes() {
    insta::assert_snapshot!(line_count_file_print_all("multiple_item_attributes.rs"), @r"
    Category           | Detailed contents              |

    # multiple_item_attributes.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | #[verus_verify]
                       |                                | #[verus::trusted]
    Spec               | FunctionSpec                   | #[verus_spec(ret => ensures ret == x)]
    Trusted            | Code(Exec Signature Body(Exec  | fn trusted_identity(x: u64) -> u64 {
    Trusted            | Code(Exec) Body(Exec)          |     x
    Trusted            | Code(Exec) Body(Exec)          | }
                       |                                |
                       |                                | fn main() {}

    | file                        | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-----------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | multiple_item_attributes.rs |       3 |    1 |     0 |    0 | 0          | 0       | 0      | 6           |
    |-----------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total                       |       3 |    1 |     0 |    0 | 0          | 0       | 0      | 6           |
    ");
}

#[test]
fn test_trusted() {
    insta::assert_snapshot!(line_count_file_print_all("trusted.rs"), @r"
    Category           | Detailed contents              |

    # trusted.rs
                       |                                | use vstd::prelude::*;
                       |                                |
                       |                                | verus! {
                       |                                |
    Trusted            | Directive                      | #[verifier::external_body]
    Trusted            | Code(Exec Signature Body(Exec  | fn new_style() {}
                       |                                |
    Trusted            | Directive                      | #[verifier(external_body)]
    Trusted            | Code(Exec Signature Body(Exec  | fn old_style() {}
                       |                                |
    Trusted            | Directive                      | #[verifier::external_fn_specification]
    Trusted            | Code(Exec Signature Body(Exec  | pub fn ex_swap<T>(a: &mut T, b: &mut T) {
    Trusted            | Code(Exec) Body(Exec)          |     core::mem::swap(a, b)
    Trusted            | Code(Exec) Body(Exec)          | }
                       |                                |
    Trusted            | FunctionSpec                   | pub assume_specification<T>[ core::mem::replace::<T> ](dest: &mut T, src: T) -> T;
                       |                                |
                       |                                | #[verifier(external)]
                       |                                | fn ignored() {}
                       |                                |
    Proof              | Code(Proo Signature Body(Proo  | proof fn assumptions(x: u64) {
    Trusted            | Code(Proo Assumptio Body(Proo  |     assume(x < 100);
    Trusted            | Code(Proo Assumptio Body(Proo  |     admit();
    Proof              | Code(Proof) Body(Proof)        | }
                       |                                |
                       |                                | } // verus!

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
    Proof              | Signature(Exec)                |     i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Proof              | Signature(Exec)                |     j: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Exec               | Signature(Exec)                | )
    Spec               | Signature(Exec FunctionSpec    |     requires
    Spec               | Signature(Exec FunctionSpec    |         i@.constant() == a.id(),
    Spec               | Signature(Exec FunctionSpec    |         j@.constant() == b.id(),
    Spec               | Signature(Exec FunctionSpec    |         i@.namespace() != j@.namespace(),
    Exec               | Code(Exec) Body(Exec)          | {
    Proof              | Code(E Body(E Atomic OpenIn    |     open_atomic_invariant!(i.borrow() => perm_i => {
    Proof              | Code(E Body(E Atomic OpenIn    |         open_atomic_invariant!(j.borrow() => perm_j => {
    Proof Exec         | Code(E Body(E GhostT Atomic    |             b.store(Tracked(&mut perm_j), 4);
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
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |         cell.put(Tracked(&mut points_to), x_plus_2);
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
    Proof              | Signature(Exec)                |     i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Proof              | Signature(Exec)                |     Tracked(inv): Tracked<&LocalInvariant<CellId, PointsTo<u8>, EvenCell>>,
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
    | open_invariant.rs |       1 |   19 |    57 |   16 |          6 |       5 |      4 |          28 |
    |-------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total             |       1 |   19 |    57 |   16 |          6 |       5 |      4 |          28 |
    ");
}

#[test]
fn test_tracked() {
    insta::assert_snapshot!(line_count_file_print_all("tracked.rs"), @r"
    Category           | Detailed contents              |

    # tracked.rs
                       |                                | use vstd::prelude::*;
                       |                                | use vstd::atomic::*;
                       |                                |
                       |                                | verus! {
                       |                                |
    Proof Exec         | Code(Exec Signature Body(Exec  | fn foo(Tracked(perm): Tracked<&PermissionU32>, x: u32) {
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Proof Exec         | Code(Exec Signature Body(Exec  | fn bar(x: u32, Tracked(perm): Tracked<&PermissionU32>) {
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Exec               | Signature(Exec)                | fn baz(
    Proof              | Signature(Exec)                |     Tracked(perm1): Tracked<&PermissionU32>,
    Exec               | Signature(Exec)                |     x: u32,
    Proof              | Signature(Exec)                |     Tracked(perm2): Tracked<&PermissionU32>,
    Exec               | Signature(Exec)                |     y: u32,
    Exec               | Code(Exec Signature Body(Exec  | ) {
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Exec               | Code(Exec Signature Body(Exec  | fn tracked_args() {
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (a, Tracked(p)) = PAtomicU32::new(0);
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let y = a.load(Tracked(&p));
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     foo(Tracked(&p), 4);
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     bar(4, Tracked(&p));
    Exec               | Code(Exec) Body(Exec)          |     baz(
    Proof              | Code(Exec Body(Exec GhostTrac  |         Tracked(&p),
    Exec               | Code(Exec) Body(Exec)          |         4,
    Proof              | Code(Exec Body(Exec GhostTrac  |         Tracked(&p),
    Exec               | Code(Exec) Body(Exec)          |         y,
    Exec               | Code(Exec) Body(Exec)          |     );
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // Tracked parameter, with the body's opening brace on a separate line
    Proof Exec         | Signature(Exec)                | fn tracked_param_brace_separate(Tracked(perm): Tracked<&PermissionU32>, x: u32)
    Spec               | Signature(Exec FunctionSpec    |     requires
    Spec               | Signature(Exec FunctionSpec    |         x > 0,
    Exec               | Code(Exec) Body(Exec)          | {
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // Tracked struct fields
    Exec               | DatatypeDecl                   | struct Wrapper {
    Proof              | DatatypeDecl GhostTracked(P    |     perm: Tracked<PermissionU32>,
    Exec               | DatatypeDecl                   |     x: u32,
    Exec               | DatatypeDecl                   | }
                       |                                |
    Comment            | Comment                        | // Tracked return types
    Proof Exec         | Code(Exec Signature Body(Exec  | fn ret_named() -> (t: Tracked<PermissionU32>) {
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (a, Tracked(p)) = PAtomicU32::new(0);
    Proof              | Code(Exec Body(Exec GhostTrac  |     Tracked(p)
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Proof Exec         | Code(Exec Signature Body(Exec  | fn ret_unnamed() -> Tracked<PermissionU32> {
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (a, Tracked(p)) = PAtomicU32::new(0);
    Comment            | Comment                        |     // below is counted as Proof Exec -- after ghost erasure, would still have return;
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     return Tracked(p);
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Trusted            | Directive                      | #[verifier::external_body]
    Trusted            | Code(Exec Signature Body(Exec  | fn ret_tup() -> ((Tracked<PermissionU32>, Tracked<PermissionU32>)) {
    Trusted            | Code(Exec) Body(Exec)          |     (Tracked::assume_new(), Tracked::assume_new())
    Trusted            | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // Variable bindings with Tracked or tracked
    Exec               | Code(Exec Signature Body(Exec  | fn tracked_bindings() {
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (a, Tracked(p1)) = PAtomicU32::new(0);
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (b, Tracked(p2)) = PAtomicU32::new(0);
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (c, Tracked(p3)) = PAtomicU32::new(0);
    Proof              | Code(Exec Body(Exec GhostTrac  |     let tracked q1 = p1;
    Proof              | Code(Exec Body(Exec GhostTrac  |     let t1 = Tracked(q1);
    Proof              | Code(Exec Body(Exec GhostTrac  |     let Tracked(q1) = t1;
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let w = Wrapper { perm: Tracked(q1), x: 1 };
    Exec               | Code(Exec) Body(Exec)          |     let y = Wrapper {
    Proof              | Code(Exec Body(Exec GhostTrac  |         perm: Tracked(p2),
    Exec               | Code(Exec) Body(Exec)          |         x: 1
    Exec               | Code(Exec) Body(Exec)          |     };
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let o = Some(Tracked(p3));
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let (Tracked(v1), Tracked(v2)) = ret_tup();
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // Tracked nested inside other types
    Exec               | DatatypeDecl                   | struct OptWrapper {
    Proof Exec         | DatatypeDecl GhostTracked(P    |     opt: Option<Tracked<PermissionU32>>,
    Exec               | DatatypeDecl                   | }
                       |                                |
    Proof Exec         | Code(Exec Signature Body(Exec  | fn nested_param(o: Option<Tracked<&PermissionU32>>) {
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Proof Exec         | Code(Exec Signature Body(Exec  | fn nested_ret() -> (t: Option<Tracked<PermissionU32>>) {
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |     let v: Vec<Tracked<PermissionU32>> = Vec::new();
    Exec               | Code(Exec) Body(Exec)          |     None
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
                       |                                | } // verus!

    | file       | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | tracked.rs |       4 |    2 |    10 |   30 |         22 |       6 |      0 |          19 |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total      |       4 |    2 |    10 |   30 |         22 |       6 |      0 |          19 |
    ");
}
