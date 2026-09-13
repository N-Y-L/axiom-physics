# Verification and scope

Review date: 2026-09-13. This is an internal verification record; no external peer review is claimed.

The main declaration is
`Adiabatic.finite_dimensional_adiabatic_theorem` in
[`Adiabatic/MainTheorem.lean`](../Adiabatic/MainTheorem.lean). It proves the
proposition `FiniteDimensionalAdiabaticTheorem E` defined in
[`Adiabatic/Statement.lean`](../Adiabatic/Statement.lean).

## Precisely what is proved

For each finite-dimensional complex Hilbert space and each supplied
`GappedHamiltonian`:

- The fixed paths `H` and `P` are globally `C²` in real time.
- `H` is self-adjoint. `P` is a self-adjoint idempotent and commutes with `H`.
- A fixed `g > 0` separates every real eigenvalue in the selected sector from
  every real eigenvalue in its complement, throughout `[0,1]`.
- The physical equation is `U' = (-iT) H U`, with `U(0)=I` and `T>0`.

The theorem constructs a solution of this equation and proves

$$
\exists C\ge0\;\forall T>0\;\forall U\text{ solving the equation}\;
\forall s\in[0,1],\qquad
\|(I-P(s))U(s)P(0)\|\le C/T.
$$

The norm is the Hilbert-space operator norm of continuous complex linear
maps. The constant is chosen before the runtime, the physical solution, and
the time. Thus the conclusion is uniform in all three of those variables.
The selected subspace may have arbitrary rank, and internal degeneracy or
crossing does not violate the hypotheses. The zero-dimensional case is
included.

The companion theorem `GappedHamiltonian.exists_unique_unitary_evolution`
in [`Adiabatic/Schrodinger.lean`](../Adiabatic/Schrodinger.lean) states existence,
uniqueness on the unit interval, and unitarity explicitly.
[`Adiabatic/Examples.lean`](../Adiabatic/Examples.lean) constructs a two-level
example with energies `0` and `1`, gap `1`, and a selected projection proved
to be neither zero nor the identity. This verifies that the input structure
admits a nontrivial instance.

## Proof review

The semantic review checked the complete chain, including the declarations
used by the final proof:

1. The numerical spectral gap implies that the two invariant sectors have no
   common eigenvalue. Self-adjointness ensures that the eigenvalues used in
   the finite-dimensional spectral theorem are real.
2. `SpectralGap.lean` constructs an invertible operator on the fixed space of
   operators. It acts as the identity on diagonal blocks and as the
   Hamiltonian commutator on off-diagonal blocks. An eigenbasis is used only
   at a fixed time.
3. `Regularity.lean` applies smooth inversion and constructs a `C¹` solution
   `X` of `[H,X]=[P',P]`. Compactness supplies bounds on `X`, its actual
   within-interval derivative, and the Kato generator. These paths and
   bounds precede the choice of runtime.
4. `Propagator.lean` constructs the physical and comparison evolutions from
   continuous coefficients. Its Picard argument works on the whole unit
   interval and imposes no smallness requirement on `T H`.
5. `Transport.lean` derives unitarity from the skew-adjoint evolution
   equation and finite dimensionality. It derives exact projection
   intertwining from projection differentiation.
6. `Evolution.lean`, `Bounds.lean`, and `Comparison.lean` obtain the
   inverse-runtime estimate from the derivative of a corrected comparison
   curve. The signs agree with `U'=(-iT)HU`, `[A,B]=AB-BA`, and
   `K=[P',P]`.
7. `Leakage.lean` uses exact intertwining and the contraction property of
   orthogonal projections. The final theorem applies this estimate to every
   physical solution. For a subsingleton operator space, the leakage norm is
   zero directly.

The full theorem does not assume a commutator solution, an auxiliary
propagator, unitarity, exact transport, or an adiabatic error estimate. Those
are intermediate conclusions. Pointwise inversion on the unit interval is
sufficient: smoothness is needed at invertible values, and all derivative
claims used at the endpoints are within the interval.

## Mechanical verification

The implementation is pinned to Lean `v4.28.0` and mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The main theorem and the supporting
modules have compiled successfully with this toolchain. The complete library build passed with warnings treated as errors:
`lake --wfail build`. The public build entry point is `lake build`.

The full theorem's transitive axiom audit reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, the standard classical foundations used
by mathlib. It reports no added theorem axiom or `sorryAx`. The audit also
checked the main components, the spectral bridge, propagator existence,
comparison estimate, and the nontrivial example.

Compilation and semantic review address different questions: Lean checks
that the proof inhabits its declared type; the review above checks that this
type expresses the intended adiabatic theorem. The axiom audit makes the
foundational dependencies explicit. These checks establish the supplied
statement, rather than any broader unformalized version of the theorem.

## Limits of the result

The smooth projection path is supplied as part of the input. The repository
does not yet construct this path from a Hamiltonian and a spectral-band
selection rule. Global `C²` paths are a convenient stronger hypothesis than
regularity on a neighborhood of `[0,1]`.

The theorem supplies an existential constant `C`; it does not formalize an
explicit optimal dependence on `g`, `‖H'‖`, `‖H''‖`, dimension, or selected
rank. It does not treat unbounded operators, infinite-dimensional Hilbert
spaces, gapless evolution, switching improvements, or exponentially small
errors. Optional calculations in the proof plan are not additional checked
theorems unless a corresponding declaration is identified.

This is a formalization of a classical mathematical result. Any claim about
being the first formalization requires the separate prior-art search and its
stated search limits; the correctness review here establishes no priority
claim.

The [saved verification record](../checks/results.json) includes source hashes.
The final integrity run audited 25 public declarations and scanned all 17
project Lean files. Temporary rejection checks confirmed that an unfinished
proof and a theorem depending on a new axiom both fail the audit. The
GitHub workflow is configured but has not run before publication.

The compiled project proofs were also rechecked successfully with
`LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic`. This uses Lean’s bundled
checker and is not a claim of verification by a separately implemented prover.
