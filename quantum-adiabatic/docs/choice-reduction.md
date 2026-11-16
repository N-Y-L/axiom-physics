# Choice and the adiabatic theorem

The common-domain theorem compares the supplied Banach domain norm with the
physical graph norm of each Hamiltonian. Without choice, a bounded linear
bijection need not have a bounded inverse. The foundations results identify
this comparison as the relevant obstruction.

Here ZF is classical set theory without the axiom of choice. Completeness
means convergence of proper Cauchy filters, not merely of Cauchy sequences.
Let QAT denote the exact common-domain theorem, with its supplied Banach domain,
constructed spectral projection and strong unitary evolution, bounded domain
lifts, and both uniform $C/T$ estimates.

## Written mathematical results

The following implications are proved in the linked notes:

$$
\mathrm{AC}_{\omega}\ \Longrightarrow\ \mathrm{QAT}
\ \Longleftrightarrow\ \mathrm{BI}(B,H)
\ \Longrightarrow\ \mathrm{CMC}.
$$

Countable choice, $\mathrm{AC}_{\omega}$, selects an element from each set in
a countable family of nonempty sets. Countable multiple choice, CMC, selects
a finite nonempty subset from each. The bounded inverse principle
$\mathrm{BI}(B,H)$ says that every bounded complex-linear bijection from a
Banach space to a Hilbert space has a bounded inverse.

The [bounded-inverse characterization](foundations/bounded-inverses.md)
uses a constant doubled-swap Hamiltonian. Its strong evolution transfers
one coordinate to the other; the theorem's bounded domain lift then supplies
a bounded inverse. Conversely, the inverse principle supplies graph control,
and the [analytic construction](foundations/analytic-constructions.md)
gives the full theorem.

The [countable-choice proof](foundations/countable-choice.md) supplies the
upper bound. The [CMC counterexample](foundations/countable-multiple-choice.md)
gives the lower bound, including a version using the actual initial graph
norm. The earlier [Dedekind-finite-real counterexample](foundations/necessity.md)
also remains available.

There are useful positive restrictions. [Explicit graph control](foundations/graph-control.md)
suffices in ZF. A [well-orderable dense subset of the physical Hilbert space](foundations/separable-spaces.md)
also suffices, even with an arbitrary supplied Banach domain norm. In
particular, physical separability suffices. Infinite dimension alone therefore
does not establish a need for choice.

These are written mathematical proofs, **not Lean formalizations**. The
[operator consequences](foundations/operator-consequences.md) include a
closed graph characterization and an infinite partial-choice result for
families of uniformly bounded finite cardinality. That partial result is
not a choice function on the whole family. Whether CMC suffices, countable
choice is necessary, or another familiar principle is exactly equivalent
remains unresolved.

## Lean results

The full theorem retains axioms `[propext, Classical.choice, Quot.sound]`.
Its statement and proof are unchanged.

The eight `Adiabatic/Foundations/` modules use ordinary mathlib foundations.
They formalize prefix-support extraction, the strong swap equations and
inverse extraction, and conservation and linearity for supplied trajectories.
`bounded_inverse_of_doubled_adiabatic_theorem` constructs the exact gapped
Hamiltonian and applies the original theorem predicate to obtain a bounded
inverse. This is a checked implication in ordinary Lean foundations; it is
not a ZF formalization of the displayed equivalence or the CMC lower bound.

All 202 declarations in `Adiabatic/ChoiceReduction/`, including generated
helpers, have audited dependencies contained in `[propext, Quot.sound]`.
They cover explicit-inverse algebra, finite selections and product estimates,
and symmetry and involution obstructions. The last involution selector
theorem explicitly assumes decidable equality. These components do not
constitute a choice-free analytic adiabatic theorem.

The [Lean audit](foundations/lean-audit.md) gives exact scopes, checked types,
and dependency paths. The weighted-space ZF constructions, the complete
analytic implications in a choice-free foundation, and the inner-model
argument for separable physical spaces remain unformalized.
