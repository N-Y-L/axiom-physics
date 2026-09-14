# Proof modules

The public import is `import Adiabatic`. It includes all proof modules.
The principal result is
[`Unbounded.common_domain_adiabatic_theorem`](Unbounded/MainTheorem.lean);
read its [statement](Unbounded/Statement.lean) before the supporting proofs.

## Common-domain theorem

`Unbounded/` treats arbitrary complex Hilbert spaces and Hamiltonians that
may be unbounded in the physical norm.

| Part | Modules |
| --- | --- |
| Statement and final theorem | [Statement](Unbounded/Statement.lean), [MainTheorem](Unbounded/MainTheorem.lean) |
| Domain and resolvents | [Domain](Unbounded/Domain.lean), [Resolvent](Unbounded/Resolvent.lean), [ResolventSpectrum](Unbounded/ResolventSpectrum.lean), [BoundedPerturbation](Unbounded/BoundedPerturbation.lean) |
| Spectral projections | [RieszProjection](Unbounded/RieszProjection.lean), [ContourIndependence](Unbounded/ContourIndependence.lean), [MovingBand](Unbounded/MovingBand.lean) |
| Domain-valued commutator | [RieszCommutator](Unbounded/RieszCommutator.lean), [SmoothGluing](Unbounded/SmoothGluing.lean), [GlobalCommutator](Unbounded/GlobalCommutator.lean), [GappedCommutator](Unbounded/GappedCommutator.lean) |
| Autonomous evolution | [ResolventApproximation](Unbounded/ResolventApproximation.lean), [Autonomous](Unbounded/Autonomous.lean) |
| Time-dependent evolution | [Propagator](Unbounded/Propagator.lean), [RightPropagator](Unbounded/RightPropagator.lean), [TimeSlicing](Unbounded/TimeSlicing.lean), [FrozenEvolution](Unbounded/FrozenEvolution.lean), [FrozenApproximation](Unbounded/FrozenApproximation.lean), [Nonautonomous](Unbounded/Nonautonomous.lean) |
| Domain control in the limit | [GraphBounds](Unbounded/GraphBounds.lean), [FrozenGraphBounds](Unbounded/FrozenGraphBounds.lean), [NonautonomousDomain](Unbounded/NonautonomousDomain.lean), [HilbertGraphConvergence](Unbounded/HilbertGraphConvergence.lean), [GraphLimit](Unbounded/GraphLimit.lean) |
| Strong calculus and transport | [StrongCalculus](Unbounded/StrongCalculus.lean), [StrongEstimate](Unbounded/StrongEstimate.lean), [Evolution](Unbounded/Evolution.lean), [Transport](Unbounded/Transport.lean) |
| Comparison and error bounds | [Comparison](Unbounded/Comparison.lean), [Perturbation](Unbounded/Perturbation.lean), [CommutatorTheorem](Unbounded/CommutatorTheorem.lean), [UniformComparison](Unbounded/UniformComparison.lean), [GappedSpectralTheorem](Unbounded/GappedSpectralTheorem.lean), [GappedReduction](Unbounded/GappedReduction.lean) |

## Bounded Hamiltonians in arbitrary dimension

For bounded Hamiltonians in arbitrary dimension,
[SpectralTheorem](Infinite/SpectralTheorem.lean) combines
[RieszProjection](Infinite/RieszProjection.lean),
[RieszCommutator](Infinite/RieszCommutator.lean),
[Unitary](Infinite/Unitary.lean), and
[CommutatorTheorem](Infinite/CommutatorTheorem.lean).

## Original finite-dimensional theorem

For the original finite-dimensional theorem, start with
[Statement](Statement.lean),
[MainTheorem](MainTheorem.lean), [Schrodinger](Schrodinger.lean), and the
[two-level example](Examples.lean).

The remaining files prove projection, spectral-gap, regularity, propagator,
transport, and comparison results.
[ReducedResolvent](ReducedResolvent.lean) gives a separate algebraic special
case. [ProjectionDistance](ProjectionDistance.lean) is shared by the broader
theorems.

## Choice-reduction components

[ChoiceReduction.lean](ChoiceReduction.lean) imports the supporting modules:

| Module | Result |
| --- | --- |
| [ExplicitInverse](ChoiceReduction/ExplicitInverse.lean) | Specified inverses, resolvent identities, and reduced commutator algebra |
| [FiniteSelection](ChoiceReduction/FiniteSelection.lean) | Existential selection over a supplied finite index set |
| [FiniteProducts](ChoiceReduction/FiniteProducts.lean) | Contractive product comparison from local errors |
| [MixedProducts](ChoiceReduction/MixedProducts.lean) | Product comparison with separate physical and domain bounds |
| [ChoicePrinciples](ChoiceReduction/ChoicePrinciples.lean) | Conditional equivalences of selection and inverse principles |
| [LiftObstruction](ChoiceReduction/LiftObstruction.lean) | A lift of the coordinate swap supplies an inverse and its bound |
| [SymmetryObstruction](ChoiceReduction/SymmetryObstruction.lean) | Equivariant maps preserve fixed points and cannot orient symmetric pair data |
| [InvolutionObstruction](ChoiceReduction/InvolutionObstruction.lean) | Fixed-point and equivariant-selector obstructions for two additive involutions |

Their [separate audit](../checks/ChoiceReductionAxioms.lean) excludes
`Classical.choice`. The [research note](../docs/choice-reduction.md) states
their hypotheses and the limits of their application to the full theorem.

## Foundations components using mathlib's ordinary axioms

[Foundations.lean](Foundations.lean) imports the components below. Their
transitive dependencies include `Classical.choice`; they are covered by
the ordinary project audit and do not alter the stricter choice-reduction audit.

| Module | Result |
| --- | --- |
| [PrefixMultipleChoice](Foundations/PrefixMultipleChoice.lean) | Finite nonempty sets of prefixes at unbounded lengths give finite nonempty subsets at every index |
| [PrefixSupport](Foundations/PrefixSupport.lean) | Summable coefficients with unbounded active prefix levels give countable multiple choice |
| [SwapScalarEvolution](Foundations/SwapScalarEvolution.lean) | Scalar integrating factor and forced quarter-turn coordinate transfer |
| [StrongSwapObstruction](Foundations/StrongSwapObstruction.lean) | The actual strong-propagator equation forces a domain-lift norm lower bound; arbitrarily large witnesses exclude a propagator |
| [SwapExtraction](Foundations/SwapExtraction.lean) | Continuous-linear-map specialization of phased swap inverse extraction |
| [StrongSwapInverse](Foundations/StrongSwapInverse.lean) | An actual strong swap propagator supplies a bounded inverse, using Hilbert-valued coordinate equations |
| [TrajectoryAssembly](Foundations/TrajectoryAssembly.lean) | Strong trajectories preserve inner products; uniqueness forces linearity and physical boundedness of a supplied family |
| [DoubledSwap](Foundations/DoubledSwap.lean) | Constructs the original self-adjoint gapped Hamiltonian and derives a bounded inverse from the exact adiabatic theorem predicate |

The [written ZF reductions](../docs/choice-reduction.md) also require weighted
Hilbert spaces and their completeness. Those constructions and the
set-theoretic implications are not formalized by these components.

See the [proof guide](../docs/proof-guide.md) for the mathematical argument
and the [documentation index](../docs/README.md) for research, verification,
and proposed extensions.
