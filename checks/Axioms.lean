import Adiabatic.MainTheorem
import Adiabatic.Examples
import Adiabatic.ReducedResolvent
import Adiabatic.Schrodinger
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Audit the trusted dependencies of the public results

Run `lake build` before `lake env lean checks/Axioms.lean`.

Each command traverses the checked declaration's type and proof recursively, including
imported dependencies. It fails if the closure contains anything beyond Lean's standard
propositional extensionality, classical choice, and quotient soundness principles.
The accompanying source scan is supplementary; this dependency check is authoritative.
-/

open Lean Elab Command

/-- Check the transitive dependency closure, then print it using Lean's standard command. -/
elab "audit_axioms " decl:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let actual ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := actual.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Untrusted dependencies in {name}: {unexpected.toList}"
  elabCommand (← `(#print axioms $decl))

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

#check @Adiabatic.finite_dimensional_adiabatic_theorem
