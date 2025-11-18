## Meeting 13.11.2025

Inbetween projects, thought about threating logically atomic functions as physically atomic to aid resolution of prophesy variables
- $\text{Resolve}(e, p, w)$ requires expr $e$ to be physically atomic
    - it would be nice if logatom was sufficiant
    - **possible:** invent a new notion of "resolve-logatom" alongside "inv-logatom" (does not scale)
    - **ideal:** allow logically atomic exprs to be treated as physically atomic
- motivating example was RDCSS (see [The Future is Ours](https://plv.mpi-sws.org/prophecies/paper.pdf))
- came up with $\bold{atomic}(e)$ which behaves like $e$ but prevents execution from switch threads
    - later implemented in [Program Logics à la Carte](https://dl.acm.org/doi/pdf/10.1145/3704847)
- wanted to prove refinement $e \preccurlyeq \bold{atomic}(e)$ where $e$ is logically atomic
    - requires notion of linearisability
    - the AU is a purely theoretical object, not a physical linearisation point
    - needs to reason about reordering events
    - proof deemed not feasable

*Intuitively,* there should be a transformation between logically atomic and a physically atomic spec
- should look like $\lang P\rang\{P'\}\;e\;\lang Q\rang\{Q'\}\;\leadsto\;\{P''\}^\bold{at!}\,e\;\{Q''\}$
- There must be a restriction on $e$ and its hoare triple to do this transformation, otherwise any non logically atomic expression would be physically atomic
    - e.g. $\{P\}\;e\;\{Q\} \;\leadsto\;\lang\top\rang\{P\}\;e\;\lang\top\rang\{Q\} \;\leadsto\;\{P\}^\bold{at!}\,e\;\{Q\}$ would be bad
- We believe the private pre and post conditions should be trivial (i.e. empty or pure)
    - in Verus, this corresponds to no permissions in the function signature
- **...but** we also want to pass atomic invariants to the function
- Possible rule: All `tracked` arguments must be `Clone`
    - :V: `Tracked<&AtomicInvariant>`
    - :X: `Tracked<PermissionU64>`
    - :X: `Tracked<&mut PermissionU64>`
    - :V: `Tracked<&PermissionU64>` (excludes `&mut` to same permission)
- Argument types must be checked recursively

Possibly related papers:
- [Compilation of Linearizable Data Structures](https://hal.science/hal-01538128/file/SimuLin.pdf)
- [Theorems for Free from Separation Logic Specifications](https://iris-project.org/pdfs/2021-icfp-intensional-final.pdf)
- [CRIS: The Power of Imagination in Specification and Verification](https://dl.acm.org/doi/abs/10.1145/3703595.3710846)
