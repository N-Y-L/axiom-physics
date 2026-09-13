# Prior-art assessment: quantum adiabatic theorem in Lean

Search date: **13 September 2026**. This report records a bounded public-source search, including direct inspection of source archives at the revisions listed below. It does not establish worldwide priority.

## Finding and decision

**No complete, publicly inspectable formalization of a quantum adiabatic theorem was found in the sources searched.** There is relevant prior work: a PhysAtlas page reports checked Lean projection-calculus identities, and a public Lean project studies the dark state of a spatial adiabatic passage Hamiltonian. Neither provides a checked adiabatic convergence or error theorem in the evidence inspected. This supports pursuing a carefully scoped formalization, with explicit credit for existing mathematics and formal infrastructure. It does not support claiming that nobody has done the work.

Two catalogs independently leave the target unlinked. The David–Palsberg *Top 100 Quantum Theorems* lists the adiabatic theorem as item 22 without a formal-proof link; its page reports an update on 10 September 2026. Mathlib's theorem catalog contains `Q356895: title: Adiabatic theorem` without a `decl` field at the inspected revision. Catalog omissions are supporting evidence, not exhaustive searches of completed or ongoing research. [1, 2]

The useful research objective is a kernel-checked theorem connecting a slowly varying Hamiltonian's Schrödinger evolution to its instantaneous spectral subspace. A matrix identity, an assumed estimate, or a convergence theorem derived from an assumed adiabatic bound is a building block. The final achievement must identify which analytic assumptions and existence results are proved and which are supplied.

## Evidence matrix

| Source | Evidence inspected | Actual status relevant to this project |
| --- | --- | --- |
| Mathlib 4 | Complete source archive; theorem catalog; ODE and spectral documentation | No quantum adiabatic theorem found; substantial reusable analysis and linear algebra |
| Physlib, including PhyslibAlpha and QuantumInfo | Complete source archive at one immutable revision | No adiabatic or Kato theorem found by the recorded lexical scan; thermodynamic adiabatic relations and Berry references are unrelated matches |
| PhysAtlas projection-calculus page | Provider's public declaration preview and scope exclusions | Reports three checked Lean identities; explicitly excludes the quantum adiabatic theorem; proof bodies and checker logs unavailable in the public view |
| Spatial Adiabatic Passage project | Both public `.lean` files and complete repository tree | Dark-state and matrix claims; adiabatic theorem explicitly unproved; one separate angle proof contains `sorry`; no reproducible Lake project configuration found |
| Isabelle AFP | Quantum-information and quantum-computing catalogs; relevant entries | Adjacent spectral, measurement, circuit, and register results; no adiabatic theorem found in this catalog/search coverage |
| QWIRE and SQIR | Complete source archives at immutable revisions | No `adiabatic` or whole-word `Kato` matches in scanned source/documentation files |
| HOL Light | Complete source archive at an immutable revision | No `adiabatic` or whole-word `Kato` matches in scanned source/documentation files |

## Closest positive results

### PhysAtlas: Kato projection calculus

The public page *Finite-Dimensional Kato Projection Calculus Seed* reports the declarations `idempotentDerivative_add`, `idempotentDerivative_sandwich_zero`, and `katoGenerator_commutator_projection_eq_derivative` in the namespace `PhysAtlasFormalizations.Quantum.KatoProjectionCalculus`. These concern differentiating an idempotent operator path and recovering its derivative through a double commutator. This is directly adjacent to the proposed Kato proof route. [3]

The page expressly excludes spectral-projection construction, isolated eigenvalue branches, gap estimates, transport ODEs, propagator intertwining, and adjointness side conditions. It also expressly excludes an adiabatic theorem. The provider labels the Lean result checked, but the page does not expose proof bodies, checker logs, or an immutable source revision. The defensible classification is **reported checked preliminary identities, not independently rebuilt here**. No publication or first-proof date was established. Its search-engine crawl time is not a publication date. [3]

Credit this work when describing overlapping formal projection identities. Independently proving elementary identities from standard mathematical sources is reasonable, but their existence should not be presented as a new discovery. The review has not obtained reusable licensed source from PhysAtlas; no such code is incorporated into this repository.

### Spatial adiabatic passage: a narrower and incomplete Lean project

The repository `zuwasi/Spatial-Adiabatic-Passage-Ultracold-Atoms` was created on 16 July 2026 according to GitHub metadata. At revision `543799ad43951684d371a4e1284c7b2764452de9`, it contains `lean/DarkState.lean` and `lean/SAP.lean`. The first gives proof scripts for a three-by-three real Hamiltonian's unnormalized dark-state equation, zero middle component, symmetry, and nonnegative squared coupling expression. These are finite matrix facts, not control of a time-dependent Schrödinger solution. [4, 5]

The second file discusses a positive spectral-gap condition, but its adiabatic section explicitly states that the theorem has not been proved. Although comments describe an axiom, the inspected section actually supplies prose and a positive-gap predicate, not a complete formal adiabatic statement. A later, separate endpoint mixing-angle proof contains `sorry`. There is no proof of an adiabatic error bound, limiting evolution, or quantitative population transfer. [5]

The complete 26-file tree contains no `lakefile.lean`, `lakefile.toml`, `lake-manifest.json`, or `lean-toolchain`, despite README build instructions. The README also identifies demonstration terminal logs as simulated. We did not rebuild these proof scripts and therefore do not endorse a reproducible verification claim. Their relevant status is **public preliminary source with an explicitly missing adiabatic theorem**. [4, 5]

### Existing physics and quantum-information libraries

Physlib is now the combined repository for the former PhysLean and Lean-QuantumInfo projects. Its primary README distinguishes a curated core, a lighter-review PhyslibAlpha, and the QuantumInfo codebase. The inspected tree includes Hilbert-space, spectral-theory, self-adjoint operator, and Hermitian-matrix material. A proposed dependency should be assessed module by module and pinned to a tested revision; the name of a library is not sufficient evidence that all intended analytic bridges already exist. [6]

Isabelle's AFP already contains a finite-dimensional simultaneous diagonalization result, projective measurements and CHSH, the uncertainty principle, quantum and classical registers, and related quantum-information developments. These demonstrate substantial formal quantum mathematics, but the inspected entry descriptions and subject catalogs did not identify the target theorem. This review did not scan every AFP theory or all private Isabelle work. [7–9]

QWIRE and SQIR provide established Rocq/Coq quantum-programming infrastructure. Their source scans produced no recorded adiabatic/Kato matches. An additional public project, `ethanlee515/Hamiltonian-simulation-formalization`, explicitly limits its stated scope to time-independent Hamiltonians and proposes symbolic matrix-exponential semantics. It is relevant background, not a located proof of the slowly varying Hamiltonian theorem. [10–12]

## Search coverage and reproducibility

The strongest negative evidence is the direct archive scan below. GitHub recursive trees for mathlib, Physlib, and the SAP repository reported `truncated: false`. Archive contents were inspected without executing repository code or adding third-party source to this project.

| Repository | Immutable revision | Files scanned | Result |
| --- | --- | ---: | --- |
| `leanprover-community/mathlib4` | `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a` | 9,206 | One hit: unlinked adiabatic theorem catalog entry |
| `leanprover-community/physlib` | `c76e3ccab04eacb69a126ca5c021b0788d513292` | 912 | Ten matching lines: ideal-gas thermodynamics or Berry references |
| `inQWIRE/QWIRE` | `6cb3e5acdf3cc7351ac839c2339f5124a160cc31` | 25 | No matches |
| `inQWIRE/SQIR` | `134fb942265091baa3e3972f78f72da41827351f` | 91 | No matches |
| `jrh13/hol-light` | `2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32` | 600 | No matches |

For mathlib and Physlib, the scan selected `.lean`, `.md`, `.yaml`, `.yml`, `.toml`, and `.bib` files, searching case-insensitively for `adiabatic`, whole-word `Kato`, `adiabatisch`, or `adiabatique`. For QWIRE, SQIR, and HOL Light, it selected `.v`, `.ml`, `.md`, `.thy`, `.rst`, `.tex`, and `.bib`, searching for `adiabatic` or whole-word `Kato`. File counts include selected documentation, not just theorem files. The precise archive endpoints are GitHub's `codeload.github.com/<owner>/<repo>/tar.gz/<revision>`; immutable browsable source references are provided below. [2, 6, 10, 11, 13]

GitHub's public repository-metadata search returned:

| Query | Matches | Interpretation |
| --- | ---: | --- |
| `adiabatic language:Lean` | 0 | No matching repository metadata with Lean as GitHub's language filter |
| `adiabatic lean` | 1 | The SAP repository, whose principal language is HTML |
| `adiabatic formalization` | 0 | No repository metadata match |
| `adiabatic formalisation` | 0 | No repository metadata match |
| `adiabatic coq` | 0 | No repository metadata match |
| `adiabatic isabelle` | 0 | No repository metadata match |
| `quantum adiabatic theorem` | 3 | Educational/simulation repositories; no complete formal proof identified |
| `PhysAtlas` | 0 | No repository metadata match; public website nevertheless found |

All these API responses reported `incomplete_results: false`. That flag describes the query response, not the completeness of the research. **Repository search is not global code search.** The SAP and PhysAtlas positives illustrate why zero-result language or repository queries are insufficient.

Web searches included exact phrases combining “adiabatic theorem” or “quantum adiabatic” with “Lean,” “Lean4,” “Mathlib,” “formalization,” “formalisation,” “formalized,” “proof assistant,” “machine-checked,” “Isabelle,” “Coq,” “Rocq,” “HOL Light,” and “HOL4.” Domain-specific searches covered GitHub, the Lean community documentation and public Zulip index, and `isa-afp.org`. Hits were followed to primary pages or source where relevant. Many “formalization” hits meant ordinary mathematical formulation; many “adiabatic” hits concerned thermodynamics, numerical simulation, or unrelated names.

The search is strongest for the inspected Lean libraries. It is weaker for HOL4, non-GitHub repositories, unpublished work, unindexed branches, recent pull requests, and proofs using different vocabulary. The third-party projects were not compiled. These limits prevent a universal absence or priority claim.

## Consequences for the formalization

The initial finite-dimensional gapped theorem is now proved in this repository. The selected starting point used mathlib's spectral theorem for symmetric operators, including an orthonormal eigenvector basis. Public ODE documentation also exposes existence and uniqueness results based on Picard–Lindelöf and Grönwall, while distinguishing local existence from uniqueness on larger intervals. The implementation constructs global propagators explicitly rather than treating an ODE import as an existence proof. [14, 15]

The implementation uses operator-product calculus, interval integration, spectral theory, and operator-norm estimates. The pinned mathlib revision governs which declarations are available; current online documentation can describe a later module layout. The [proof guide](proof-guide.md) records the actual dependencies and identifies the distinction between source inspection and checked project declarations.

The completed extension constructs differentiable spectral projections from an actual unbounded common-domain Hamiltonian and a continuously moving isolated band. It derives the global smooth commutator solution and constructs nonautonomous strong evolution from $C^1$ common-domain regularity and self-adjointness. The declaration `Adiabatic.Unbounded.common_domain_adiabatic_theorem` then proves uniform projection-distance and leakage estimates from the Hamiltonian and gap assumptions. The [common-domain research report](unbounded-research.md) explains the Kato–Yosida foundations and full proof chain; [verification.md](verification.md) records the mechanical audit. This mathematical extension does not strengthen the prior-art search into a worldwide absence claim.

Jansen–Ruskai–Seiler provide conventional quantitative estimates with explicit gap dependence, while Avron–Elgart give a gapless theorem with different hypotheses and no general rate in its basic conclusion. They are distinct mathematical targets. This repository proves a common-domain uniformly gapped band theorem with an existential constant, as specified in its statement and proof guide; it does not claim every version of “the quantum adiabatic theorem.” [16, 17]

Suggested public novelty wording:

> This repository formalizes a uniformly gapped quantum adiabatic theorem for possibly unbounded self-adjoint Hamiltonians on a fixed common domain. Our public-source review of 13 September 2026 did not locate a complete existing formalization of the quantum adiabatic theorem in the sources searched. Related projection-calculus and quantum-information formalizations already exist. This is a bounded prior-art assessment, not a claim of worldwide priority.

Before making any stronger publication claim, repeat the search and seek community confirmation through the relevant maintainers or formalization communities. No outreach was sent during this review. A final release should link the exact theorem statement, tested toolchain, immutable source, build evidence, and axiom audit, and clearly distinguish the target theorem from supporting lemmas.

## Primary sources

1. Marco David and Jens Palsberg, [Top 100 Quantum Theorems](https://marcodavid.net/top100/), item 22; page reports updated 10 September 2026. Accessed 13 September 2026.
2. Mathlib, [theorem catalog at the inspected revision](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/docs/1000.yaml#L376); [complete source tree](https://github.com/leanprover-community/mathlib4/tree/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a).
3. PhysAtlas, [Finite-Dimensional Kato Projection Calculus Seed](https://www.physatlas.ai/pages/quantum.adiabatic.kato_projection_calculus/). Publication date and public source revision not established; accessed 13 September 2026.
4. Zuwasi, [Spatial Adiabatic Passage repository at the inspected revision](https://github.com/zuwasi/Spatial-Adiabatic-Passage-Ultracold-Atoms/tree/543799ad43951684d371a4e1284c7b2764452de9), including README and tree; GitHub repository creation metadata dated 16 July 2026.
5. Zuwasi, [SAP.lean](https://github.com/zuwasi/Spatial-Adiabatic-Passage-Ultracold-Atoms/blob/543799ad43951684d371a4e1284c7b2764452de9/lean/SAP.lean) and [DarkState.lean](https://github.com/zuwasi/Spatial-Adiabatic-Passage-Ultracold-Atoms/blob/543799ad43951684d371a4e1284c7b2764452de9/lean/DarkState.lean), inspected source, not rebuilt.
6. Physlib community, [source tree and README at the inspected revision](https://github.com/leanprover-community/physlib/tree/c76e3ccab04eacb69a126ca5c021b0788d513292).
7. Archive of Formal Proofs, [Quantum information catalog](https://isa-afp.org/topics/mathematics/physics/quantum-information/) and [Quantum computing catalog](https://www.isa-afp.org/topics/computer-science/algorithms/quantum-computing/), accessed 13 September 2026.
8. Mnacho Echenim, [Simultaneous diagonalization of pairwise commuting Hermitian matrices](https://isa-afp.org/entries/Commuting_Hermitian.html), AFP, 18 July 2022; [Quantum projective measurements and the CHSH inequality](https://isa-afp.org/entries/Projective_Measurements.html), AFP, 3 March 2021.
9. Alexander Treml, [Uncertainty Principle](https://isa-afp.org/entries/Uncertainty_Principle.html), AFP, 26 March 2024; Dominique Unruh, [Quantum and Classical Registers](https://isa-afp.org/entries/Registers.html), AFP, 28 October 2021.
10. inQWIRE, [QWIRE at the inspected revision](https://github.com/inQWIRE/QWIRE/tree/6cb3e5acdf3cc7351ac839c2339f5124a160cc31).
11. inQWIRE, [SQIR at the inspected revision](https://github.com/inQWIRE/SQIR/tree/134fb942265091baa3e3972f78f72da41827351f).
12. Ethan Lee, [Hamiltonian-simulation-formalization](https://github.com/ethanlee515/Hamiltonian-simulation-formalization), README scope, accessed 13 September 2026. No immutable revision or build audited for this peripheral project.
13. John Harrison and contributors, [HOL Light at the inspected revision](https://github.com/jrh13/hol-light/tree/2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32).
14. Mathlib, [InnerProductSpace.Spectrum documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Spectrum.html), accessed 13 September 2026.
15. Mathlib, [ODE.ExistUnique documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/ExistUnique.html), accessed 13 September 2026.
16. Sabine Jansen, Mary-Beth Ruskai, and Ruedi Seiler, [Bounds for the adiabatic approximation with applications to quantum computation](https://arxiv.org/abs/quant-ph/0603175v3), *Journal of Mathematical Physics* 48, 102111 (2007); version 3, 8 November 2007.
17. J. E. Avron and A. Elgart, [Adiabatic Theorem without a Gap Condition](https://arxiv.org/abs/math-ph/9805022v4), *Communications in Mathematical Physics* 203, 445–463 (1999); version 4, 19 April 1999.
