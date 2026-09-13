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

The [overview](choice-reduction.md) explains the role of choice and graph norms,
and separates mathematical arguments from Lean-checked components.

| Resource | Contents |
| --- | --- |
| [Necessity](foundations/necessity.md) | Counterexample to the initial-graph-norm theorem in ZF and its weak choice consequence. |
| [Dependent choice](foundations/dependent-choice.md) | Proof of the original theorem in ZF + DC. |
| [Explicit graph control](foundations/graph-control.md) | ZF proof with an additional graph inequality at every time. |
| [Lean audit](foundations/lean-audit.md) | Supporting formal results, their statements, and transitive dependencies. |

For local verification commands, see the [repository README](../README.md).
For editing conventions, see [Contributing](../CONTRIBUTING.md).
