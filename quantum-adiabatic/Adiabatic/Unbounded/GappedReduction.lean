import Adiabatic.Unbounded.GappedSpectralTheorem
import Adiabatic.Unbounded.BoundedPerturbation

/-!
# Reduction to common-domain evolution existence

The Kato correction is continuously differentiable and skew-adjoint.
It therefore gives a bounded self-adjoint perturbation of the original
Hamiltonian. Existence for continuously differentiable common-domain
self-adjoint Hamiltonians supplies both evolutions needed by the spectral
estimate.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E}

/-- The bounded Kato correction constructed from the spectral band. -/
def GappedHamiltonian.katoCorrection (data : GappedHamiltonian domain) (t : ℝ) : E →L[ℂ] E :=
  katoGenerator (data.spectralProjection t)
    (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t)

/-- The spectral assumptions make the Kato correction continuously differentiable. -/
theorem GappedHamiltonian.katoCorrection_contDiff (data : GappedHamiltonian domain) :
    ContDiffOn ℝ 1 data.katoCorrection (Icc (0 : ℝ) 1) := by
  have hp := data.spectralProjection_contDiff
  have hd := hp.derivWithin (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hp₁ := hp.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact (hd.mul hp₁).sub (hp₁.mul hd)

/-- The constructed Kato correction is skew-adjoint. -/
theorem GappedHamiltonian.katoCorrection_star (data : GappedHamiltonian domain)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    star (data.katoCorrection t) = -data.katoCorrection t := by
  exact star_katoGenerator_of_hasDerivWithinAt
    (fun _ hu => (data.spectralProjection_isStarProjection hu).2) ht
    (uniqueDiffOn_Icc_zero_one t ht)
    (((data.spectralProjection_contDiff.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)

/-- Incorporating a bounded correction into the Hamiltonian gives exactly
the same strong evolution equation. -/
def StrongPropagator.of_bounded_correction
    {H : ℝ → D →L[ℂ] E} {K : ℝ → E →L[ℂ] E} {z : ℂ} (hz : z ≠ 0)
    (U : StrongPropagator domain (fun t => H t + (z⁻¹ • K t).comp domain.inclusion)
      (fun _ => 0) z) : StrongPropagator domain H K z where
  evolution := U.evolution
  lift := U.lift
  inverseLift := U.inverseLift
  initial := U.initial
  isUnitary := U.isUnitary
  preserves_domain := U.preserves_domain
  inverse_preserves_domain := U.inverse_preserves_domain
  strong_continuous := U.strong_continuous
  domain_continuous := U.domain_continuous
  strong_derivative x t ht := by
    have hd := U.strong_derivative x t ht
    rw [U.preserves_domain t ht]
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, add_zero,
      smul_add, smul_smul, mul_inv_cancel₀ hz, one_smul] using hd

/-- The evolution-existence statement used by the spectral theorem.
Proved in `Adiabatic.Unbounded.MainTheorem`. -/
def CommonDomainEvolutionExistence (domain : CommonDomain D E) : Prop :=
  ∀ H : ℝ → D →L[ℂ] E, ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1) →
    (∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) →
    ∀ T : ℝ, 0 < T →
      Nonempty (StrongPropagator domain H (fun _ => 0) (-Complex.I * (T : ℂ)))

/-- General common-domain evolution existence supplies the Kato propagator. -/
theorem GappedHamiltonian.exists_kato_propagator_of_evolution_existence
    (data : GappedHamiltonian domain) (hexists : CommonDomainEvolutionExistence domain)
    {T : ℝ} (hT : 0 < T) :
    Nonempty (StrongPropagator domain data.H data.katoCorrection (-Complex.I * (T : ℂ))) := by
  let z : ℂ := -Complex.I * (T : ℂ)
  have hz : z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hT.ne')
  have hzstar : star z = -z := by simp [z]
  let H' : ℝ → D →L[ℂ] E := fun t =>
    data.H t + (z⁻¹ • data.katoCorrection t).comp domain.inclusion
  have hH' : ContDiffOn ℝ 1 H' (Icc (0 : ℝ) 1) := by
    apply (data.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).add
    exact ((((ContinuousLinearMap.compL ℂ D E E).flip domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn
      (data.katoCorrection_contDiff.const_smul z⁻¹)
  have hsa : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H' t) := by
    intro t ht
    exact domain.isSelfAdjoint_add_skew_correction (data.H t) (data.selfAdjoint t ht)
      (data.katoCorrection t) (data.katoCorrection_star ht) z hzstar
  obtain ⟨U⟩ := hexists H' hH' hsa T hT
  exact ⟨U.of_bounded_correction hz⟩

/-- Once the general common-domain existence theorem is supplied, all parts
of the full gapped adiabatic theorem follow from the proved spectral calculus. -/
theorem commonDomainAdiabaticTheorem_of_evolution_existence
    (hexists : CommonDomainEvolutionExistence domain) : CommonDomainAdiabaticTheorem domain := by
  intro data
  refine ⟨data.spectralProjection_contDiff, (fun _ ht => data.spectralProjection_isStarProjection ht),
    (fun T hT => hexists data.H (data.smooth.of_le (by norm_num)) data.selfAdjoint T hT), ?_⟩
  obtain ⟨C, hC, hbound⟩ := data.exists_adiabatic_estimates_of_strong_propagators
  refine ⟨C, hC, ?_⟩
  intro T hT U t ht
  obtain ⟨V⟩ := data.exists_kato_propagator_of_evolution_existence hexists hT
  exact hbound T hT U V t ht

end Adiabatic.Unbounded
