# Documentation

Start with the full common-domain theorem: it treats possibly unbounded
self-adjoint Hamiltonians on an arbitrary complex Hilbert space, constructs
the band projection and strong unitary evolution, and proves uniform
operator-norm error bounds $C/T$. The original finite-dimensional theorem
remains available with its own input structure and two-level example.

## Read the theorem and proof

| Resource | Contents |
| --- | --- |
| [Full formal statement](../Adiabatic/Unbounded/Statement.lean) | Common-domain, $C^2$, and uniformly gapped bounded-band assumptions; constructed projection and error estimates. |
| [Full theorem](../Adiabatic/Unbounded/MainTheorem.lean) | Main proof, general evolution existence, and uniqueness of the physical evolution. |
| [Proof guide](proof-guide.md) | Full common-domain argument first, followed by the bounded and original finite-dimensional proofs. |
| [Verification and scope](verification.md) | Exact mathematical scope, verification record, and limits of the checks. |
| [Common-domain research](unbounded-research.md) | Primary literature, assumption comparison, spectral calculus, and evolution construction. |

## Further reading

| Resource | Contents |
| --- | --- |
| [Original finite-dimensional statement](../Adiabatic/Statement.lean) and [proof](../Adiabatic/MainTheorem.lean) | Smooth supplied Hamiltonian and projection paths, spectral-sector separation, and leakage estimate. |
| [Two-level example](../Adiabatic/Examples.lean) | A nontrivial instance of the original finite-dimensional input structure. |
| [Possible extensions](extensions.md) | Informal explicit-gap and reduced-resolvent estimates, with proposed work separated from proved declarations. |
| [Prior work](prior-art.md) | Sources searched for existing formalizations and limits of the search. |
| [Publication](publication.md) | Release description and publication instructions. |

For local verification commands, see the [repository README](../README.md).
For editing conventions, see [Contributing](../CONTRIBUTING.md).
