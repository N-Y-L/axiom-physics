import Adiabatic.MainTheorem
import Adiabatic.Examples
import Adiabatic.ReducedResolvent
import Adiabatic.Schrodinger
import Adiabatic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Audit the trusted dependencies of the public results

Run `lake build` before `lake env lean checks/Axioms.lean`.

The project audit selects declarations by their originating module, including private
declarations and declarations outside the `Adiabatic` namespace. It traverses their
types and proofs recursively, including imported dependencies, and rejects unsafe
project declarations. The named checks below also print the public results' dependencies.
The audit fails if any closure contains anything beyond Lean's standard propositional
extensionality, classical choice, and quotient soundness principles.
The accompanying source scan is supplementary; this dependency check is authoritative.
-/

open Lean Elab Command

/-- Audit all declarations originating in the project library, regardless of namespace. -/
elab "audit_project_axioms" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun declarations name info =>
    match env.getModuleIdxFor? name with
    | some index =>
        if (`Adiabatic).isPrefixOf env.header.moduleNames[index.toNat]! then
          declarations.push (name, info)
        else declarations
    | none => declarations
  if declarations.isEmpty then
    throwError "No declarations from the Adiabatic project modules were found"
  for (name, info) in declarations do
    if info.isUnsafe then
      throwError "Unsafe project declaration: {name}"
  -- Sharing the visited set avoids retraversing mathlib for every declaration.
  let collect : Lean.CollectAxioms.M Unit :=
    declarations.forM fun (name, _) => Lean.CollectAxioms.collect name
  let (_, state) := (collect.run env).run {}
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := state.axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in project declarations: {unexpected.toList}"
  logInfo m!"Audited all {declarations.size} declarations from the Adiabatic project modules"

/-- Check the transitive dependency closure, then print it using Lean's standard command. -/
elab "audit_axioms " decl:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := actual.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in {name}: {unexpected.toList}"
  elabCommand (← `(#print axioms $decl))

audit_project_axioms

-- 2026-09-14: explicit components of the countable-multiple-choice investigation.
audit_axioms Adiabatic.Foundations.countableMultipleChoice_of_unbounded_prefix_choices
audit_axioms Adiabatic.Foundations.not_unbounded_prefix_choices_of_not_countableMultipleChoice
audit_axioms Adiabatic.Foundations.finite_positive_threshold_of_summable
audit_axioms Adiabatic.Foundations.countableMultipleChoice_of_unbounded_active_prefix_levels
audit_axioms Adiabatic.Foundations.finite_active_levels_of_not_countableMultipleChoice
audit_axioms Adiabatic.Foundations.finite_active_levels_of_square_summable_of_not_countableMultipleChoice
audit_axioms Adiabatic.Foundations.bounded_active_levels_of_square_summable_of_not_countableMultipleChoice
audit_axioms Adiabatic.Foundations.inverseFromSwapLift
audit_axioms Adiabatic.Foundations.inverseFromSwapLift_right
audit_axioms Adiabatic.Foundations.inverseFromSwapLift_left
audit_axioms Adiabatic.Foundations.bounded_inverse_of_swap_lift
audit_axioms Adiabatic.Foundations.scalar_integrating_factor
audit_axioms Adiabatic.Foundations.swap_quarter_turn_coordinates
audit_axioms Adiabatic.Foundations.strongPropagator_swap_coordinates
audit_axioms Adiabatic.Foundations.strongPropagator_swap_lift_norm_lower
audit_axioms Adiabatic.Foundations.no_strongPropagator_of_unbounded_swap_coordinates
audit_axioms Adiabatic.ChoiceReduction.equivariant_map_preserves_fixed_point
audit_axioms Adiabatic.ChoiceReduction.no_equivariant_map_to_fixed_point_free_action
audit_axioms Adiabatic.ChoiceReduction.equivariant_pair_map_equal_coordinates
audit_axioms Adiabatic.ChoiceReduction.no_equivariant_pair_selector
audit_axioms Adiabatic.ChoiceReduction.equivariant_antisymmetric_pair_output_zero
audit_axioms Adiabatic.ChoiceReduction.unique_solution_fixed_by_symmetry

audit_axioms Adiabatic.projection_derivative
audit_axioms Adiabatic.katoGenerator_commutator_of_hasDerivWithinAt
audit_axioms Adiabatic.star_katoGenerator_of_hasDerivWithinAt
audit_axioms Adiabatic.transport_mem_unitary_of_finiteDimensional
audit_axioms Adiabatic.kato_transport_intertwines_of_finiteDimensional
audit_axioms Adiabatic.gapSuperoperator_isUnit
audit_axioms Adiabatic.commutatorSolution_katoGenerator
audit_axioms Adiabatic.hasDisjointSectorEigenvalues_of_gap
audit_axioms Adiabatic.exists_contDiffOn_commutator_of_spectral_separation
audit_axioms Adiabatic.exists_uniform_bounds
audit_axioms Adiabatic.exists_solution_unitInterval
audit_axioms Adiabatic.exists_propagator_unitInterval
audit_axioms Adiabatic.hasDerivWithinAt_correctedEvolution
audit_axioms Adiabatic.adiabatic_comparison
audit_axioms Adiabatic.leakage_le_comparison
audit_axioms Adiabatic.reducedResolvent_commutator
audit_axioms Adiabatic.exists_adiabatic_bound_of_commutator
audit_axioms Adiabatic.GappedHamiltonian.hasSchrodingerEvolution
audit_axioms Adiabatic.GappedHamiltonian.hasUniformAdiabaticEstimate
audit_axioms Adiabatic.finite_dimensional_adiabatic_theorem
audit_axioms Adiabatic.exists_schrodingerEvolution
audit_axioms Adiabatic.schrodingerEvolution_unitary
audit_axioms Adiabatic.schrodingerEvolution_unique
audit_axioms Adiabatic.GappedHamiltonian.exists_unique_unitary_evolution
audit_axioms Adiabatic.Examples.exists_nontrivial_gappedHamiltonian
audit_axioms Adiabatic.transport_mem_unitary
audit_axioms Adiabatic.exists_unitary_propagator_unitInterval
audit_axioms Adiabatic.Infinite.bounded_adiabatic_theorem_of_resolvent_contour
audit_axioms Adiabatic.projection_distance_le_comparison
audit_axioms Adiabatic.Unbounded.CommonDomain.graphEquiv
audit_axioms Adiabatic.Unbounded.CommonDomain.shift_bijective
audit_axioms Adiabatic.Unbounded.CommonDomain.physicalResolvent_star
audit_axioms Adiabatic.Unbounded.CommonDomain.isSelfAdjoint_add_bounded
audit_axioms Adiabatic.Unbounded.CommonDomain.rieszProjection_isStarProjection
audit_axioms Adiabatic.Unbounded.CommonDomain.contDiffOn_rieszProjection
audit_axioms Adiabatic.Unbounded.CommonDomain.contourCommutator_commutator
audit_axioms Adiabatic.Unbounded.CommonDomain.contDiffOn_contourCommutatorLift
audit_axioms Adiabatic.Unbounded.CommonDomain.exists_autonomous_strongPropagator
audit_axioms Adiabatic.Unbounded.CommonDomain.exists_domain_vector_of_tendsto_of_shift_bound
audit_axioms Adiabatic.Unbounded.hasDerivWithinAt_apply_of_strong
audit_axioms Adiabatic.Unbounded.hasDerivWithinAt_inverse_apply_of_strong
audit_axioms Adiabatic.Unbounded.StrongPropagator.adjoint_strong_derivative
audit_axioms Adiabatic.Unbounded.StrongPropagator.unique
audit_axioms Adiabatic.Unbounded.hasDerivWithinAt_correctedEvolution_apply
audit_axioms Adiabatic.Unbounded.corrected_curve_bound_of_denseRange
audit_axioms Adiabatic.Unbounded.strong_adiabatic_comparison
audit_axioms Adiabatic.Unbounded.strong_transport_intertwines
audit_axioms Adiabatic.Unbounded.exists_adiabatic_bound_of_strong_commutator
audit_axioms Adiabatic.Unbounded.strong_propagator_perturbation
audit_axioms Adiabatic.Unbounded.norm_timeOrderedProduct_sub_comp_le
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.spectralProjection_isStarProjection

audit_axioms Adiabatic.Unbounded.CommonDomain.exists_autonomousGroup
audit_axioms Adiabatic.Unbounded.CommonDomain.rieszProjection_eq_of_spectral_membership
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.spectralProjection_contDiff
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.spectralProjectionLift_contDiff
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.exists_contDiffOn_commutatorLift
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.exists_adiabatic_estimates_of_strong_propagators
audit_axioms Adiabatic.Unbounded.commonDomainAdiabaticTheorem_of_evolution_existence
audit_axioms Adiabatic.Unbounded.CommonDomain.tendsto_domain_of_tendsto_inclusion_of_shift_norm_upper
audit_axioms Adiabatic.Unbounded.FrozenFamily.strong_right_derivative
audit_axioms Adiabatic.Unbounded.FrozenFamily.lift_inverseLift_eq_increment
audit_axioms Adiabatic.Unbounded.exists_frozenApproximation

audit_axioms Adiabatic.Unbounded.exists_unitary_limit_of_right_approximations
audit_axioms Adiabatic.Unbounded.hasDerivWithinAt_right_approximation_limit
audit_axioms Adiabatic.Unbounded.FrozenApproximation.continuousOn_limit_lift
audit_axioms Adiabatic.Unbounded.exists_nonautonomous_strongPropagator
audit_axioms Adiabatic.Unbounded.common_domain_evolution_existence
audit_axioms Adiabatic.Unbounded.common_domain_adiabatic_theorem
audit_axioms Adiabatic.Unbounded.GappedHamiltonian.exists_unique_unitary_evolution

#check @Adiabatic.Unbounded.common_domain_adiabatic_theorem
#check @Adiabatic.finite_dimensional_adiabatic_theorem

audit_axioms Adiabatic.Foundations.swap_quarter_turn_values
audit_axioms Adiabatic.Foundations.strongPropagator_swap_coordinate_maps
audit_axioms Adiabatic.Foundations.bounded_inverse_of_strong_swap
audit_axioms Adiabatic.Foundations.domainTrajectory_inner_constant
audit_axioms Adiabatic.Foundations.domainTrajectory_norm_constant
audit_axioms Adiabatic.Foundations.domainTrajectory_unique
audit_axioms Adiabatic.Foundations.domainTrajectory_family_add
audit_axioms Adiabatic.Foundations.domainTrajectory_family_smul
audit_axioms Adiabatic.Foundations.domainTrajectory_physicalMap
audit_axioms Adiabatic.Foundations.domainTrajectory_physicalMap_apply

audit_axioms Adiabatic.ChoiceReduction.involution_eq_neg_of_trivial_fixed_points
audit_axioms Adiabatic.ChoiceReduction.involutions_comp_eq_self_of_trivial_fixed_points
audit_axioms Adiabatic.ChoiceReduction.trivial_of_three_trivial_fixed_spaces
audit_axioms Adiabatic.ChoiceReduction.no_equivariant_nonzero_selector_for_two_involutions
audit_axioms Adiabatic.Foundations.doubledInclusion_bijective
audit_axioms Adiabatic.Foundations.physicalSwap_selfAdjoint
audit_axioms Adiabatic.Foundations.doubledDomain_operator
audit_axioms Adiabatic.Foundations.doubledHamiltonian_selfAdjoint
audit_axioms Adiabatic.Foundations.physicalSwap_pencil_identity
audit_axioms Adiabatic.Foundations.physicalSwap_pencil_bijective
audit_axioms Adiabatic.Foundations.doubledHamiltonian_spectrum_subset
audit_axioms Adiabatic.Foundations.doubledHamiltonian_spectrum_eq
audit_axioms Adiabatic.Foundations.bounded_inverse_of_doubled_adiabatic_theorem
