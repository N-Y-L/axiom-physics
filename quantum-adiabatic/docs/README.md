# Documentation

The common-domain theorem treats possibly unbounded Hamiltonians on an
arbitrary complex Hilbert space. The finite-dimensional theorem has a
separate input structure and two-level example.

## Read the theorem and proof

| Resource | Contents |
| --- | --- |
| [Formal statement](../Adiabatic/Unbounded/Statement.lean) | Common-domain, $C^2$, and uniformly gapped bounded-band assumptions; constructed projection and error estimates. |
| [Full theorem](../Adiabatic/Unbounded/MainTheorem.lean) | Main proof, general evolution existence, and uniqueness of the physical evolution. |
| [Proof guide](proof-guide.md) | Full common-domain argument first, followed by the bounded and original finite-dimensional proofs. |
| [Verification](verification.md) | Theorem assumptions, verification record, and limits of the checks. |
| [Common-domain research](unbounded-research.md) | Primary literature, assumption comparison, spectral calculus, and evolution construction. |

## Further reading

| Resource | Contents |
| --- | --- |
| [Original finite-dimensional statement](../Adiabatic/Statement.lean) and [proof](../Adiabatic/MainTheorem.lean) | Smooth supplied Hamiltonian and projection paths, spectral-sector separation, and leakage estimate. |
| [Two-level example](../Adiabatic/Examples.lean) | A nontrivial instance of the original finite-dimensional input structure. |
| [Possible extensions](extensions.md) | Informal explicit-gap and reduced-resolvent estimates. |

## Foundations

The [overview](choice-reduction.md) separates written mathematical arguments
from Lean-checked components and states the remaining choice-strength question.

| Resource | Contents |
| --- | --- |
| [Bounded inverses](foundations/bounded-inverses.md) | ZF characterization of the exact theorem by the Banach-to-Hilbert bounded inverse principle. |
| [Countable choice](foundations/countable-choice.md) | A sufficient choice principle for the original theorem. |
| [Countable multiple choice](foundations/countable-multiple-choice.md) | Necessary choice principle, including the initial-graph-norm obstruction. |
| [Separable physical spaces](foundations/separable-spaces.md) | ZF result for physical spaces with a well-orderable dense subset and arbitrary supplied Banach domains. |
| [Analytic constructions](foundations/analytic-constructions.md) | Choice accounting for graph control, spectral projections, evolution, and estimates. |
| [Explicit graph control](foundations/graph-control.md) | ZF proof under an additional graph inequality at every time. |
| [Operator consequences](foundations/operator-consequences.md) | Closed graph, uniform boundedness, and the limits of partial-choice arguments. |
| [Lean audit](foundations/lean-audit.md) | Formal components, checked types, and transitive dependencies. |
| [Dedekind-finite-real obstruction](foundations/necessity.md) | Earlier counterexample and its weak choice consequence. |
| [Dependent choice](foundations/dependent-choice.md) | Earlier sufficient foundation for the original theorem. |
| [Bounded lifts](foundations/bounded-lifts.md) | Auxiliary bounded-inverse extraction argument. |

For local verification commands, see the [repository README](../README.md).
For editing conventions, see [Contributing](../CONTRIBUTING.md).
