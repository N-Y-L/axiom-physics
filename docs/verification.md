# Verification and scope

Review date: 2026-09-13. The reviews were internal. There has been no external
peer review.

The main declaration is
`Adiabatic.Unbounded.common_domain_adiabatic_theorem` in
[Unbounded/MainTheorem.lean](../Adiabatic/Unbounded/MainTheorem.lean). It proves
`CommonDomainAdiabaticTheorem domain`, defined in
[Unbounded/Statement.lean](../Adiabatic/Unbounded/Statement.lean).

## The theorem

Let $E$ be any complete complex Hilbert space. A common domain consists of a
complete complex Banach space $D$ and a continuous injective inclusion
$j:D\to E$ with dense range. The hypotheses are:

- $H(s):D\to E$ is twice continuously differentiable in operator norm on
  $[0,1]$.
- The partially defined physical operator with domain $j(D)$ and action
  $j\psi\mapsto H(s)\psi$ is self-adjoint for every $s\in[0,1]$.
- Continuous real functions $a(s)<b(s)$ select a bounded spectral band.
  Both endpoints are at distance at least $g>0$ from every point of the
  spectrum, uniformly on $[0,1]$.

Self-adjointness means equality with mathlib's unbounded adjoint of a
`LinearPMap`, including equality of domains. The domain norm is proved equivalent to
the graph norm of each self-adjoint Hamiltonian. No Hilbert structure on
$D$, separability of $E$, finite dimension, finite rank, or compact resolvent
is required.

The theorem constructs the spectral projection $P(s)$ by a resolvent
integral and proves that it is an orthogonal projection and $C^2$. Although
the band endpoints are only continuous, local fixed contours give the
projection's differentiability.

For every $T>0$, the theorem constructs a `StrongPropagator` with $U_T(0)=I$.
Its physical evolution is unitary and strongly continuous. Both $U_T(s)$
and its inverse preserve the whole common domain. The domain lift is
strongly continuous in the Banach norm of $D$, and for every $\psi\in D$,

$$
\frac{d}{ds}U_T(s)j\psi=-iT H(s)\widetilde U_T(s)\psi,
\qquad j\widetilde U_T(s)\psi=U_T(s)j\psi.
$$

Derivatives at the endpoints are within $[0,1]$. The theorem does not assert
operator-norm differentiability of $U_T$ in the physical Hilbert space.
The companion `GappedHamiltonian.exists_unique_unitary_evolution` proves
uniqueness of the physical evolution among strong unitary common-domain
propagators on this interval.

There is a constant $C\ge0$, independent of $T>0$, the choice of physical
propagator, and $s\in[0,1]$, such that

$$
\begin{aligned}
\|U_T(s)P(0)U_T(s)^*-P(s)\|&\le C/T,\\
\|(I-P(s))U_T(s)P(0)\|&\le C/T.
\end{aligned}
$$

These are norms of continuous complex linear maps $E\to E$. Internal band
degeneracies and crossings are allowed. Empty selected bands and the
zero-dimensional Hilbert space are included.

## Proof review

The review traced each construction from the theorem's hypotheses.

1. `Domain.lean` identifies the full physical operator domain and proves
   graph norm equivalence. The resolvent modules derive nonreal resolvents,
   spectral reality, spectral mapping, and smooth inverse dependence from
   self-adjointness.
2. `RieszProjection.lean`, `ContourIndependence.lean`, and `MovingBand.lean`
   construct the orthogonal band projection and its $C^2$ lift $E\to D$.
   The bounded normal resolvent $(H-i)^{-1}$ supplies continuous functional
   calculus; the unbounded spectral gap gives the contour separation.
3. `RieszCommutator.lean` constructs local solutions of $[H,X]=[P',P]$.
   `SmoothGluing.lean`, `GlobalCommutator.lean`, and `GappedCommutator.lean`
   combine them into a global $C^1$ domain-valued solution.
4. `ResolventApproximation.lean` constructs commuting bounded self-adjoint
   approximations. `Autonomous.lean` proves their unitary exponentials
   converge to a group on the whole real line. Negative times give the
   inverse; domain invariance and the strong equation are proved.
5. `FrozenEvolution.lean` composes autonomous groups on finer time grids
   and proves the right strong equation at partition boundaries.
   `FrozenGraphBounds.lean` gives uniform forward and inverse domain bounds
   and sharp two-time graph estimates. `FrozenApproximation.lean`
   constructs the approximation data from $C^1$ common-domain regularity.
6. `Nonautonomous.lean` obtains strong limits of both evolutions and
   adjoints. Adjoint-domain maximality gives domain membership.
   `GraphLimit.lean` and `HilbertGraphConvergence.lean` prove strong domain
   continuity from a sharp graph bound. A quadratic local comparison with the
   frozen autonomous group gives the time-dependent strong derivative at
   every point of the closed interval.
7. `StrongCalculus.lean`, `Evolution.lean`, `Comparison.lean`, and
   `Transport.lean` prove the corrected comparison estimate and exact
   projection transport on domain vectors, then extend the norm estimates
   by density. The signs use $U'=-iTHU$ and $K=[P',P]$.
8. `GappedReduction.lean` proves the Kato correction is $C^1$ and
   skew-adjoint. Bounded self-adjoint perturbation preserves the full
   common domain. The proved general evolution theorem therefore supplies
   both physical and Kato propagators, completing `MainTheorem.lean`.

The [research report](unbounded-research.md) compares these assumptions to
Jansen–Ruskai–Seiler, Theorem 1. The earlier
[finite-dimensional statement](../Adiabatic/Statement.lean) and
[proof](../Adiabatic/MainTheorem.lean) are unchanged. The
[two-level example](../Adiabatic/Examples.lean) uses that finite-dimensional
input structure.

## Mechanical verification

Lean is pinned to `v4.28.0` and mathlib to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The public entry point imports all
58 project proof modules. `checks/Axioms.lean` adds the audit module, for
59 Lean source files in total.

The completed verification runs are recorded with source hashes in
[checks/results.json](../checks/results.json):

- `lake --wfail build` compiles the full library with warnings treated as
  errors.
- `python3 checks/check_proofs.py` scans all project Lean sources for
  forbidden proof constructs and audits all 963 declarations originating in
  project proof modules, including private/generated declarations and names
  outside the project namespace. It also prints 69 named public checks,
  including the full unbounded theorem and nonautonomous existence.
- `python3 -m unittest discover -s checks -p 'test_*.py'` runs seven
  regression tests for the source scanner and compiled Lean rejection fixtures.
- `LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic` rechecks the compiled
  project proofs using Lean's bundled checker.

Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited
transitive dependency closures. No `sorryAx`, added theorem axiom, unsafe
declaration, or native decision procedure was found. The
[checker tests](../checks/README.md) cover forbidden constructs and valid
comments, strings, and identifiers.

Compilation checks that a proof inhabits its declared type. The axiom audit
makes its foundational dependencies explicit. The separate semantic review
checks that the type expresses the stated physical theorem. Lean's bundled
checker is not a separately implemented proof assistant. The GitHub workflow
is configured; a hosted run has not occurred before publication.

## Release review

Two further reviews of the spectral and evolution arguments found no
substantive mathematical defect. They checked the assumptions, adjoint
domains, projection, commutator, unitary limits, domain preservation,
endpoint derivatives, and uniqueness scope.

A fresh copy of the tracked sources was built without reusing project
compiled artifacts. The nine dependency builds were reused after checking
their checkouts against the pinned revisions; mathlib was not rebuilt.

The earlier text scan omitted `admit` and quoted `sorryAx`. Neither was
present in the proofs; the main-theorem axiom audits were valid. The scan
now rejects both, and the audit covers every project declaration by its
originating module. Compiled regression fixtures run in GitHub CI.

A subsequent prose revision shortened the documentation and corrected
descriptions of spectral-band boundaries and $C^1$ regularity. All 59 Lean
files match the preceding version after removing comments and normalizing
whitespace. The build, axiom audit, and bundled proof checker passed again.
The integrity checker code and its regression tests are unchanged.

## Limits

The theorem assumes a fixed common domain, $C^2$ Hamiltonian regularity, and
a uniform gap around a bounded spectral band. It does not treat changing
domains, gapless evolution, switching improvements, or exponentially small
errors. It supplies an existential constant, without an explicit optimal
dependence on the gap or derivatives of $H$.

The [prior-art search](prior-art.md) lists the sources inspected and the
limits of any priority claim.
