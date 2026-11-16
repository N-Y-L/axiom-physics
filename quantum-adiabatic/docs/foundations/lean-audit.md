# Lean components and dependency audit

The 202 declarations in `Adiabatic/ChoiceReduction/` omit `Classical.choice`
in their complete dependency closures. The eight `Adiabatic/Foundations/`
modules and the full adiabatic theorem use ordinary mathlib foundations,
including choice. The [overview](../choice-reduction.md) separates these
formal results from the written ZF arguments.

## Two foundational questions

The mathematical question is whether the theorem can be proved in classical
set theory without full AC. Replacing AC by countable choice or dependent
choice would be a weaker foundational requirement, but would not eliminate
choice altogether.

The Lean question is stricter: does a declaration's complete dependency
closure omit `Classical.choice`? Lean derives excluded middle from choice,
so even a proof using classical logic without selecting an object can fail
this audit. The audit permits `propext` and `Quot.sound` only. It introduces
no replacement axioms. A conditional theorem about a choice principle does
not assert that principle. See Lean's
[axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/) and
[account of classical reasoning](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/).

The full theorem is stated in
[common-domain statement](../../Adiabatic/Unbounded/Statement.lean): arbitrary
complex Hilbert spaces, possibly unbounded self-adjoint Hamiltonians on a
fixed dense domain, $C^2$ regularity, and a uniform gap around a bounded
spectral band. The projection and unitary evolution must be constructed,
and both operator-norm estimates must hold with one $C$ independent of
$T>0$ and $s\in[0,1]$:

$$
\|U_T(s)P(0)U_T(s)^*-P(s)\|\le C/T,
\qquad \|(I-P(s))U_T(s)P(0)\|\le C/T.
$$

## Components without Classical.choice

The sources below give the exact statements. Printed Lean types and complete
individual transitive axiom lists are recorded in
[foundations-results.json](../../checks/foundations-results.json).

| Module | All declarations, including generated helpers | Union of audited axioms |
| --- | ---: | --- |
| ExplicitInverse | 50 | `propext`, `Quot.sound` |
| FiniteSelection | 2 | `propext` |
| FiniteProducts | 39 | `propext` |
| MixedProducts | 66 | `propext`, `Quot.sound` |
| ChoicePrinciples | 21 | None |
| LiftObstruction | 11 | `propext`, `Quot.sound` |
| SymmetryObstruction | 9 | None |
| InvolutionObstruction | 4 | `propext` |

All 202 declarations omit `Classical.choice`. This audit includes dependencies
in their types. It certifies these generic algebraic statements; specializing
them to mathlib's current real or complex analytic structures reintroduces
choice through those structures.

### Explicit inverses and finite selections

[ExplicitInverse.lean](../../Adiabatic/ChoiceReduction/ExplicitInverse.lean)
retains a specified two-sided inverse as data. It proves uniqueness,
conversion to and from unit data, unique existence as a proposition, and
the noncommutative identity

$$
a^{-1}-b^{-1}=a^{-1}(b-a)b^{-1}.
$$

For a commutative scalar ring, modules $D,E$, linear maps $H,j:D\to E$,
and specified two-sided inverses $R_z,R_w:E\to D$ of $H-zj,H-wj$, it proves

$$
R_z-R_w=(z-w)R_zjR_w.
$$

It also constructs the reduced Kato commutator from an inverse of $H+P$
and the block identities $P^2=P$, $HP=PH=0$. These are algebraic results;
they do not derive inverse existence or regularity from a spectral gap.
The hypotheses are narrower than the full analytic target and are not
inserted into that target.

[FiniteSelection.lean](../../Adiabatic/ChoiceReduction/FiniteSelection.lean)
proves, for any dependent family $B_i$ indexed by `Fin n`,

$$
(\forall i<n\;\exists x\in B_i\;p_i(x))
\Longrightarrow
\exists f\in\prod_{i<n}B_i\;\forall i<n\;p_i(f_i).
$$

The proof uses induction and remains an existential proposition. It does
not extract a cardinality, obtain a finite subcover, or choose over an
infinite index set.

### Finite product estimates

[FiniteProducts.lean](../../Adiabatic/ChoiceReduction/FiniteProducts.lean)
uses a ring $A$, an ordered semiring $R$, and an explicit size
$s:A\to R$ satisfying nonnegativity, the triangle and submultiplicative
inequalities, $s(0)=0$, and $s(1)\le1$. Definiteness and completeness are
not required. Write $P_a(n)=a_{n-1}\cdots a_0$ and $P_a(0)=1$.

The product difference is the recursively constructed solution of

$$
F_0=0,\qquad F_{k+1}=a_kF_k+(a_k-b_k)P_b(k).
$$

For contractive factors $s(a_k),s(b_k)\le1$, the proved bounds are

$$
s(P_a(n)-P_b(n))\le\sum_{k<n}s(a_k-b_k)
\le\sum_{k<n}\varepsilon_k,
$$

when each local error is at most $\varepsilon_k$. A constant local bound
$\varepsilon$ gives $n\varepsilon$. The authored product definitions and
theorems have empty axiom lists. A generated constructor-injectivity
theorem uses `propext`.

[MixedProducts.lean](../../Adiabatic/ChoiceReduction/MixedProducts.lean)
extends the estimate to separate physical and domain spaces. For linear maps
$a_k:E\to E$, $b_k:D\to D$, and $j:D\to E$, supply compatible physical,
domain, and cross-space sizes. If the physical factors have size at most
one, the local mixed defects have size at most $\varepsilon_k$, and the
domain factors have size at most $\beta_k$, then

$$
s\bigl(P_a(n)j-jP_b(n)\bigr)
\le\sum_{k<n}\varepsilon_k\,\beta_{k-1}\cdots\beta_0.
$$

The empty scalar product is one. The proof derives both the defect recurrence
and domain-prefix growth; domain factors need not be contractions. The
abstract action version states the composition and size laws explicitly.
These are finite algebraic estimates. They do not construct real operator
norms, approximate evolutions, or limits.

### Inverse extraction and selection principles

[LiftObstruction.lean](../../Adiabatic/ChoiceReduction/LiftObstruction.lean)
proves the algebraic step used in the converse. Let $S:X\to Y$ be an
injective linear map over a semiring, set $j(y,x)=(y,Sx)$, and suppose a
supplied linear map $L:Y\times X\to Y\times X$ satisfies
$jL=\operatorname{swap}j$. Then

$$
R(y)=\pi_2L(y,0),\qquad SR=I_Y,\qquad RS=I_X.
$$

No surjectivity assumption on $S$ is needed. Given nonnegative $C$, a bound
$s_D(Lp)\le C s_D(p)$, and coordinate bounds
$s_X(p_2)\le s_D(p)$ and $s_D(y,0)\le s_Y(y)$, it derives
$s_X(Ry)\le C s_Y(y)$. The lift is a hypothesis of this separate algebraic
lemma, not a new hypothesis of the adiabatic theorem. Its existence is what
the mathematical converse extracts from that theorem.

[ChoicePrinciples.lean](../../Adiabatic/ChoiceReduction/ChoicePrinciples.lean)
proves three conditional equivalences for types in one universe:

- Propositional choice for arbitrary dependent families is equivalent to
  every surjection having a right inverse.
- A uniform operation selecting an element of every nonempty type is
  equivalent, in inhabitation, to a uniform operation splitting surjections.
- Uniform extraction from unique existence is equivalent, in inhabitation,
  to uniform inverse construction for bijections.

These theorems have empty axiom lists. They define and compare principles;
they do not assert any of them unconditionally. No such principle is added
to the adiabatic theorem, and no implication from that theorem to arbitrary
surjection splitting is proved.

### Symmetry and involution obstructions

[SymmetryObstruction.lean](../../Adiabatic/ChoiceReduction/SymmetryObstruction.lean)
proves that equivariant maps preserve fixed points. A fixed symmetric input
therefore cannot produce a selected element in a target where the symmetry
has no fixed point. Its nine declarations have empty axiom lists.

[InvolutionObstruction.lean](../../Adiabatic/ChoiceReduction/InvolutionObstruction.lean)
proves that an additive involution with no nonzero fixed vector is negation.
Two such involutions compose to the identity, so both involutions and their
composite cannot all have trivial fixed spaces on a nontrivial group.
The corresponding selector theorem explicitly supplies `DecidableEq V` for
its zero/nonzero split. All four declarations use only `propext`.
These statements exclude specified equivariant selectors, not every possible
construction of a choice function. See the
[selection limits](operator-consequences.md).

## Components using ordinary mathlib foundations

The following modules have combined axiom union
`[propext, Classical.choice, Quot.sound]`. Counts include generated helpers;
individual checked types and dependency lists appear in the
[current record](../../checks/foundations-results.json).

| Module | Declarations | Scope |
| --- | ---: | --- |
| PrefixMultipleChoice | 3 | Finite nonempty sets of prefixes at unbounded lengths yield finite nonempty subsets at each index. |
| PrefixSupport | 12 | Summable coefficients with unbounded active prefix levels yield the finite-prefix extraction. |
| SwapScalarEvolution | 3 | Scalar strong equations force quarter-turn coordinate transfer. |
| StrongSwapObstruction | 3 | The actual strong-propagator equation yields a domain-lift norm obstruction. |
| SwapExtraction | 7 | Continuous-linear-map inverse extraction from phased swap identities. |
| StrongSwapInverse | 4 | A strong swap propagator supplies a bounded two-sided inverse. |
| TrajectoryAssembly | 11 | Conservation, uniqueness, linearity, and a physical norm bound for supplied trajectories. |
| DoubledSwap | 36 | The exact gapped Hamiltonian is constructed and the theorem supplies its propagator. |

The prefix lemmas do not construct a ZF model or establish weighted-space
completeness. `TrajectoryAssembly` takes the trajectory family as input;
it does not prove its existence or boundedness in the supplied domain norm.
These are separate supporting statements, not new assumptions in QAT.

### The doubled-swap construction

For a bounded complex-linear bijection $j:D\to E$, the
[DoubledSwap module](../../Adiabatic/Foundations/DoubledSwap.lean) constructs
physical Hilbert space $E\oplus_2E$, Banach domain $D\times E$, and

$$
J(x,y)=(jx,y),\qquad H(x,y)=(y,jx).
$$

The physical operator is the coordinate swap on the whole Hilbert space.
The module proves self-adjointness under the original partial-operator
definition, spectrum containment in $\{-1,1\}$, and equality when $E$ is
nonzero. The constant family with band $(0,2)$ and gap $1$ satisfies the
original `GappedHamiltonian` interface, including the zero-space case.

`Adiabatic.Foundations.bounded_inverse_of_doubled_adiabatic_theorem` assumes
`CommonDomainAdiabaticTheorem (doubledDomain j hj)`, applies it to that
constructed Hamiltonian at runtime $\pi/2$, and uses the resulting strong
propagator's bounded domain lift to obtain

$$
\exists R:E\to D\text{ bounded and linear},\qquad jR=I_E,\quad Rj=I_D.
$$

The Hamiltonian, its gap, and the propagator are derived within this
implication. It uses the strong-propagator existence conjunct and its bounded
domain lift; neither $C/T$ estimate nor projection regularity is needed.
The proof uses the supplied Banach domain norm; it does not
itself establish this inverse implication with a prescribed initial graph
norm. It is checked in ordinary Lean foundations, so it does not certify
the [ZF equivalence](bounded-inverses.md) or
[CMC necessity argument](countable-multiple-choice.md).

## Where the current proof uses choice

[TraceChoice.lean](../../checks/TraceChoice.lean) searches the checked
environment and labels edges from types, definitions, proofs, and
constructors. The saved paths are in
[choice-dependencies.json](../../checks/choice-dependencies.json).

A path already occurs in the full theorem's **type**:

```text
common_domain_adiabatic_theorem
  → Complex.instRCLike → Real.normedField → Real.linearOrder
  → Classical.propDecidable → Classical.choice
```

Consequently, changing the proof body alone cannot pass the stricter audit
while retaining this elaborated type and infrastructure. Even the diagnostic
proof `(x : ℝ) : x = x := rfl` inherits all three standard axioms from the
representation. This says nothing about a mathematical need for choice to
prove reflexivity.

| Use | Current dependency | Classification |
| --- | --- | --- |
| Real order and operator norm | `Real.linearOrder`; `opNorm` through real infimum/supremum | Classical decisions and uniquely determined bounds |
| Domain identification and graph inverse | `LinearEquiv.ofInjective`, `ContinuousLinearMap.equivRange` | Unique preimages, selected over arbitrary index types |
| Inverse and adjoint definitions | `ContinuousLinearMap.inverse`, `LinearPMap.adjoint` | Classical tests of invertibility or density in totalized definitions |
| Integration | `circleIntegral → intervalIntegral → MeasureTheory.integral` | Classical integrability/completeness tests and integral construction |
| Strong limits and domain lifts | `Classical.choose` for every vector or time | Uniquely determined limits or preimages |
| Frozen evolutions | Choices indexed by time-step and mesh integers | Countable families; each individual frozen grid has finitely many effective samples |
| Local commutator solutions | Neighborhoods and solutions chosen for every point before a finite subcover | General indexed selection in the current proof |
| Graph inverse continuity | Open mapping proof selects approximate preimages | Nonunique sequential witnesses; DC suffices in the [mathematical proof](dependent-choice.md) |
| Continuous functional calculus | Character spaces and `Ideal.exists_le_maximal → … → zorn_le_nonempty₀` | A general maximal-ideal argument in this implementation |

Generic `CompleteSpace` and `cauchySeq_tendsto_of_complete` have axiom lists
`[propext, Quot.sound]`, without `Classical.choice`. Thus the trace does not
support a blanket claim that completeness requires AC. Choice enters
specific instances, constructions, and assembled families of limits.

## Scope of the reductions

The inverse proofs avoid selecting inverse data from a proposition.
They replace a use of mathlib's choice-dependent generic `map_sub` by a
direct proof from linearity and cancellation. Finite witnesses are combined
by induction. Product bounds use recursive products and sums and direct
ordered-addition laws, avoiding incidental dependencies in inferred instances.
These reductions apply to the supporting components; the established theorem's
proof has not been rewritten.

Removing choice from the full Lean proof still requires compatible scalar,
norm, adjoint, inverse, integration, and spectral-calculus definitions, then
the common-domain evolution and comparison constructions. Counting visible
`choose` calls is insufficient. No projection, propagator, commutator solution,
or error bound has been added as a hypothesis to the original theorem.

## Verification

Supporting proof modules are imported by `Adiabatic/ChoiceReduction.lean`
and `Adiabatic/Foundations.lean`. Both are imported by the public
`Adiabatic.lean` entry point. Run:

```sh
lake --wfail build
python3 checks/check_proofs.py
lake env lean checks/ChoiceReductionAxioms.lean
python3 -m unittest discover -s checks -p 'test_*.py'
LEAN_NUM_THREADS=1 lake env leanchecker Adiabatic
lake env lean checks/TraceChoice.lean
lake env lean checks/FoundationsAxioms.lean
lake env lean checks/FoundationsDependencies.lean
```

The dedicated audit selects declarations by source module, including private,
generated, and differently named declarations. It checks the complete
transitive dependencies of types and bodies. Rejection fixtures cover choice
hidden in an imported statement, imported proofs, classical logic, private
definitions, added axioms, unfinished proofs, unsafe definitions, and an
empty selection. The original integrity checks remain in force.

The warning-free build, ordinary audit of 1,244 declarations, strict audit of
202 declarations, all 15 regression tests, and bundled compiled-proof recheck
passed. The source scan covered 81 Lean files, including the standalone
diagnostics. The additional exports record all 92 declarations added by the
foundations and obstruction modules. The full theorem retains exactly
`[propext, Classical.choice, Quot.sound]`. See the
[verification note](../verification.md) and [current record](../../checks/foundations-results.json).
