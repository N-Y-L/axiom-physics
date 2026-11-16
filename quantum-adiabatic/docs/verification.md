# Verification

Verification date: 2026-09-14.

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

## Proof structure

The constructions follow from the theorem's hypotheses as follows.

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
76 project proof modules. The audits and standalone diagnostics bring the
total to 81 Lean files.

The [current record](../checks/foundations-results.json) contains verification
commands, source hashes, complete printed types for the 92 added declarations,
and their type, body, and combined axiom dependencies. It also records the
202 declarations covered by the strict audit. The
[original theorem record](../checks/results.json) and
[September 13 choice-reduction record](../checks/choice-reduction-results.json)
are preserved as historical records of their respective versions.

- `lake --wfail build` compiles the full library with warnings treated as errors.
- `python3 checks/check_proofs.py` scans all project Lean sources for forbidden
  constructs and audits all 1,244 project declarations, including private and
  generated declarations. It also prints 114 named public checks.
- `lake env lean checks/ChoiceReductionAxioms.lean` audits all 202 declarations
  in the strict supporting modules and rejects `Classical.choice` in their
  complete transitive dependencies.
- `python3 -m unittest discover -s checks -p 'test_*.py'` runs 15 regression
  tests, including compiled rejection fixtures.
- `LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic` rechecks the compiled
  project proofs using Lean's bundled checker.
- `lake env lean checks/TraceChoice.lean` traces the original implementation's
  dependencies on choice.
- `lake env lean checks/FoundationsAxioms.lean` exports checked types and
  complete axiom lists for the 92 added declarations.
- `lake env lean checks/FoundationsDependencies.lean` separates dependencies
  reached first through the checked type and through the body. Later edges
  traverse both; their union must equal Lean's combined axiom collector.

All eight commands passed. Only `propext`, `Classical.choice`, and `Quot.sound`
occur in the ordinary audit. The strict audit permits only `propext` and
`Quot.sound`. No unfinished proof, added theorem axiom, unsafe declaration,
or native decision procedure was found.

Compilation checks that a proof inhabits its declared type. The axiom audit
makes its foundational dependencies explicit. Lean's bundled checker is not
a separately implemented proof assistant. These checks verify the Lean
declarations; they do not certify the written foundations arguments.

## Build and preservation

The integrated sources were built on macOS without reusing project compiled
artifacts. All nine dependency checkouts matched their pinned revisions;
their compiled caches were reused. The full build completed 3,342 jobs.
The complete types and axiom dependencies of the 92 added declarations match
the preceding Windows verification. Raw platform logs and the original
research deliveries are retained outside the source repository.

Relative to `625685f33cb0ad7e2b8ab39ff78118a4460c4be6`, the 63 original
non-aggregate proof modules are unchanged. The original aggregate files add
imports, and the named report adds public checks. The theorem statements,
proof bodies, dependency pins, original checker logic, strict audit,
dependency tracer, regression tests, and historical verification records
are preserved. The two additional diagnostics are standalone exports.

## Foundational arguments

The [foundations notes](choice-reduction.md) give written arguments for
countable-choice sufficiency, the bounded-inverse characterization, the CMC
lower bound, and the separable-physical-space result in ZF. Their completeness
convention and any additional graph-control hypothesis are explicit. These
set-theoretic conclusions are not Lean-formalized.

The 202 `ChoiceReduction` declarations have audited dependencies contained
in `[propext, Quot.sound]`. The symmetry module's nine declarations use no
axioms; the involution module's four use only `propext`. Its final selector
theorem explicitly assumes decidable equality.

The eight `Foundations` modules use ordinary mathlib. The
[doubled-swap construction](foundations/lean-audit.md#the-doubled-swap-construction)
builds the exact gapped Hamiltonian and obtains a bounded inverse from the
propagator supplied by the original theorem predicate. This extraction uses
the bounded domain lift, not either adiabatic error estimate. It verifies the
conditional construction in standard Lean foundations. Weighted-space
completeness in ZF, the complete analytic equivalence, and the inner-model
argument remain unformalized. The full adiabatic theorem retains
`[propext, Classical.choice, Quot.sound]`.

## Limits

The theorem assumes a fixed common domain, $C^2$ Hamiltonian regularity, and
a uniform gap around a bounded spectral band. It does not treat changing
domains, gapless evolution, switching improvements, or exponentially small
errors. It supplies an existential constant, without an explicit optimal
dependence on the gap or derivatives of $H$.
