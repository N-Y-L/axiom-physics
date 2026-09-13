import Adiabatic.Unbounded.GlobalCommutator
import Adiabatic.Unbounded.MovingBand

/-!
# The commutator equation for a moving gapped spectral band

The common-domain spectral assumptions construct a globally continuously
differentiable domain-valued solution of Kato's commutator equation.
Continuous band endpoints are sufficient: fixed local contours and a finite
smooth partition of unity provide the required regularity.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Filter Metric
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E}

/-- Every time has an open neighborhood on which one fixed circle selects
the moving spectral band. -/
theorem GappedHamiltonian.exists_local_fixed_contour
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ Icc (0 : ℝ) 1 ∩ U, ∀ z ∈ sphere c r,
        z ∈ domain.resolventSet (data.H u)) ∧
      ∀ u ∈ Icc (0 : ℝ) 1 ∩ U,
        data.spectralProjection u = domain.rieszProjection (data.H u) c r := by
  have hev := (data.eventually_boundaries_close ht).and
    (data.eventually_spectralProjection_eq_fixed ht)
  obtain ⟨U, hU, htu, hsub⟩ := mem_nhdsWithin.mp hev
  refine ⟨U, hU, htu, (((data.lower t + data.upper t) / 2 : ℝ) : ℂ),
    (data.upper t - data.lower t) / 2,
    by linarith [data.band_ordered t ht], ?_, ?_⟩
  · intro u hu
    exact data.fixed_circle_resolvent_of_close hu.1 (hsub ⟨hu.2, hu.1⟩).1
  · intro u hu
    exact (hsub ⟨hu.2, hu.1⟩).2

/-- The spectral gap constructs a global C¹ domain-valued
commutator solution. -/
theorem GappedHamiltonian.exists_contDiffOn_commutatorLift
    (data : GappedHamiltonian domain) :
    ∃ L : ℝ → E →L[ℂ] D, ContDiffOn ℝ 1 L (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
        data.H t (L t (domain.inclusion x)) - domain.inclusion (L t (data.H t x)) =
          katoGenerator (data.spectralProjection t)
            (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t)
              (domain.inclusion x) := by
  exact domain.exists_contDiffOn_commutatorLift_of_local_contours isCompact_Icc
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (data.smooth.of_le (by norm_num)) data.spectralProjection_contDiff data.selfAdjoint
    (fun _ ht => data.exists_local_fixed_contour ht)

/-- The constructed spectral projection preserves the common domain and
commutes there with the unbounded Hamiltonian. -/
theorem GappedHamiltonian.spectralProjection_commutes
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    data.H t (data.spectralProjectionLift t (domain.inclusion x)) =
      data.spectralProjection t (data.H t x) := by
  have hr : 0 ≤ (data.upper t - data.lower t) / 2 := by
    linarith [data.band_ordered t ht]
  rw [spectralProjectionLift, dif_pos hr]
  exact domain.rieszProjection_commutes (data.H t) (data.selfAdjoint t ht) hr
    (data.enclosing_circle_resolvent ht) x

end Adiabatic.Unbounded
