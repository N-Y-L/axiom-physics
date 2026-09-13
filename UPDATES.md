# Updates

## 2026-09-13

Rechecked the full theorem with independent semantic reviews and a fresh
project build. Organized the documentation around the common-domain result,
added a module map, and separated proposed explicit constants from checked
proofs. Strengthened the integrity audit to cover every project declaration
and reject additional placeholder syntax; added compiled regression fixtures
and included them in CI. The mathematical statements and proofs are unchanged.


Extended the formalization to arbitrary complex Hilbert spaces and unbounded
self-adjoint Hamiltonians on a common domain. The theorem constructs the
spectral projection of a continuously moving uniformly isolated band,
constructs strong unitary evolution from $C^1$ common-domain regularity, and
proves uniform $C/T$ projection-distance and leakage bounds for $C^2$
Hamiltonians. The original finite-dimensional theorem is preserved. The
[verification note](docs/verification.md) records the build, transitive axiom
audit, and compiled-proof recheck; the [research report](docs/unbounded-research.md)
explains the exact scope and primary sources.

Proved the finite-dimensional spectral-subspace adiabatic theorem with a
uniform $C/T$ leakage estimate, assuming smooth Hamiltonian and orthogonal
spectral-projection paths with a uniform gap. Added propagator existence,
Kato transport, the spectral-gap commutator construction, and a nontrivial
two-level example. Pinned Lean 4.28.0 and mathlib, and added reproducible
build and proof-integrity checks. Research and verification records are in
`docs/`.

## Entry format

Use a dated heading and one short paragraph: what changed, its mathematical
scope, how it was checked, and any changed limitation. Link a detailed note
only when necessary.
