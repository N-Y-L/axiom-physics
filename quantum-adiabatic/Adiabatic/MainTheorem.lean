import Adiabatic.Statement
import Adiabatic.Regularity
import Adiabatic.CommutatorTheorem

/-!
# Finite-dimensional quantum adiabatic theorem

For a fixed smooth Hamiltonian and a fixed smooth orthogonal spectral
projection, a uniform spectral gap implies an operator-norm leakage bound
`C / T`. The constant is independent of the runtime and of the solution.
The physical propagator is constructed from its differential equation.
-/

noncomputable section

namespace Adiabatic

open Set

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The physical Schrödinger propagator exists for every positive runtime. -/
theorem GappedHamiltonian.hasSchrodingerEvolution (data : GappedHamiltonian E) :
    HasSchrodingerEvolution E data.H := by
  intro T _
  obtain ⟨U, hU0, hU⟩ := exists_propagator_unitInterval
    (continuousOn_const.smul data.hamiltonian_smooth.continuous.continuousOn :
      ContinuousOn (fun t => (-Complex.I * (T : ℂ)) • data.H t) (Icc (0 : ℝ) 1))
  refine ⟨U, hU0, ?_⟩
  intro t ht
  simpa only [smul_mul_assoc] using hU t ht

/-- The uniformly gapped spectral-subspace estimate, including the zero-dimensional case. -/
theorem GappedHamiltonian.hasUniformAdiabaticEstimate (data : GappedHamiltonian E) :
    HasUniformAdiabaticEstimate E data.H data.P := by
  classical
  by_cases htrivial : Subsingleton (Operator E)
  · letI := htrivial
    refine ⟨0, le_rfl, ?_⟩
    intro T _ U _ t _
    have hz : (1 - data.P t) * U t * data.P 0 = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, zero_div, le_refl]
  · haveI : Nontrivial (Operator E) := not_subsingleton_iff_nontrivial.mp htrivial
    let interval : Set ℝ := Icc 0 1
    have hinterval : UniqueDiffOn ℝ interval := uniqueDiffOn_Icc zero_lt_one
    have hH : ContDiffOn ℝ 1 data.H interval :=
      (data.hamiltonian_smooth.of_le (by norm_num)).contDiffOn
    have hP : ContDiffOn ℝ 2 data.P interval := data.projection_smooth.contDiffOn
    have hgap (t : ℝ) (ht : t ∈ interval) :
        HasDisjointSectorEigenvalues (data.H t) (data.P t) :=
      hasDisjointSectorEigenvalues_of_gap data.spectral_gap.1 (data.spectral_gap.2 t ht)
    obtain ⟨X, hX, hcomm⟩ := exists_contDiffOn_commutator_of_spectral_separation
      hH hP hinterval (fun t _ => data.hamiltonian_selfAdjoint t)
      (fun t _ => data.projection_idempotent t) (fun t _ => data.commutes t) hgap
    let dP : ℝ → Operator E := derivWithin data.P interval
    let dX : ℝ → Operator E := derivWithin X interval
    have hdPcont : ContinuousOn dP interval :=
      (hP.derivWithin hinterval (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuousOn
    have hdXcont : ContinuousOn dX interval := hX.continuousOn_derivWithin hinterval (by rfl)
    obtain ⟨C, hC, hbound⟩ := exists_adiabatic_bound_of_commutator
      data.H data.P dP X dX hH.continuousOn hdPcont hX.continuousOn hdXcont
      (fun t _ => data.hamiltonian_selfAdjoint t) (fun t _ => data.projection_selfAdjoint t)
      (fun t _ => data.projection_idempotent t) (fun t _ => data.commutes t)
      (fun t ht => ((hP.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
      (fun t ht => ((hX.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
      hcomm
    refine ⟨C, hC, ?_⟩
    intro T hT U hU
    exact hbound T hT U hU.1 hU.2

/-- The finite-dimensional quantum adiabatic theorem for a supplied smooth
orthogonal spectral projection with a uniform gap from its complement. -/
theorem finite_dimensional_adiabatic_theorem : FiniteDimensionalAdiabaticTheorem E := by
  intro data
  exact ⟨data.hasSchrodingerEvolution E, data.hasUniformAdiabaticEstimate E⟩

end Adiabatic
