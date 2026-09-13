import Adiabatic.Unbounded.GappedCommutator
import Adiabatic.Unbounded.CommutatorTheorem
import Adiabatic.Unbounded.UniformComparison
import Adiabatic.ProjectionDistance

/-!
# The spectral adiabatic estimate for unbounded Hamiltonians

The Hamiltonian's actual spectral gap constructs every spectral input to
the estimate: the orthogonal band projection, its common-domain lift, and
the smooth commutator solution. The only remaining inputs in this module
are the physical and Kato strong propagators themselves.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E}

/-- The physical and Kato evolutions stay within a uniform `C / T` in
operator norm, with every spectral input constructed from the Hamiltonian. -/
theorem GappedHamiltonian.exists_comparison_bound_of_strong_propagators
    (data : GappedHamiltonian domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ V : StrongPropagator domain data.H
        (fun t => katoGenerator (data.spectralProjection t)
          (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t))
        (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, ‖U.evolution t - V.evolution t‖ ≤ C / T := by
  obtain ⟨L, hL, hcomm⟩ := data.exists_contDiffOn_commutatorLift
  let X : ℝ → E →L[ℂ] E := fun t => domain.inclusion.comp (L t)
  have hX : ContDiffOn ℝ 1 X (Icc (0 : ℝ) 1) :=
    (((ContinuousLinearMap.compL ℂ E D E domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn hL
  have hP := data.spectralProjection_contDiff
  have hdiff := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)
  have hdP := (hP.derivWithin hdiff
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuousOn
  exact exists_comparison_bound_of_strong_commutator domain data.H
    (fun t => katoGenerator (data.spectralProjection t)
      (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t))
    X (derivWithin X (Icc (0 : ℝ) 1)) L
    ((hdP.mul hP.continuousOn).sub (hP.continuousOn.mul hdP))
    hX.continuousOn (hX.continuousOn_derivWithin hdiff (by rfl))
    (fun t ht => ((hX.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
    (fun _ _ _ => rfl) hcomm

/-- Both transported-projection distance and leakage obey the same uniform
adiabatic bound for every pair of physical and Kato strong propagators. -/
theorem GappedHamiltonian.exists_adiabatic_estimates_of_strong_propagators
    (data : GappedHamiltonian domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ _V : StrongPropagator domain data.H
        (fun t => katoGenerator (data.spectralProjection t)
          (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t))
        (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖U.evolution t * data.spectralProjection 0 * star (U.evolution t) -
          data.spectralProjection t‖ ≤ C / T ∧
        ‖(1 - data.spectralProjection t) * U.evolution t * data.spectralProjection 0‖ ≤
          C / T := by
  obtain ⟨C, hC, hbound⟩ := data.exists_comparison_bound_of_strong_propagators
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT U V t ht
  have hPderiv (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :=
    ((data.spectralProjection_contDiff.differentiableOn (by norm_num)) a ha).hasDerivWithinAt
  have hPid := fun a (ha : a ∈ Icc (0 : ℝ) 1) =>
    (data.spectralProjection_isStarProjection ha).1
  have hinter := strong_transport_intertwines V data.spectralProjection
    (derivWithin data.spectralProjection (Icc (0 : ℝ) 1)) data.spectralProjectionLift
    hPderiv (fun _ ha y => DFunLike.congr_fun (data.inclusion_spectralProjectionLift ha) y)
    (fun _ ha => data.spectralProjection_commutes ha)
    (fun a ha => katoGenerator_commutator_of_hasDerivWithinAt hPid ha
      (uniqueDiffOn_Icc_zero_one a ha) (hPderiv a ha)) ht
  have hP := data.spectralProjection_isStarProjection ht
  have hP₀ := data.spectralProjection_isStarProjection (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  constructor
  · calc
      ‖U.evolution t * data.spectralProjection 0 * star (U.evolution t) -
          data.spectralProjection t‖ ≤ 2 * ‖U.evolution t - V.evolution t‖ :=
        projection_distance_le_comparison _ _ _ _ hP₀.1 hP₀.2
          (U.isUnitary t ht) (V.isUnitary t ht) hinter
      _ ≤ 2 * (C / T) := mul_le_mul_of_nonneg_left (hbound T hT U V t ht) (by norm_num)
      _ = (2 * C) / T := by ring
  · calc
      ‖(1 - data.spectralProjection t) * U.evolution t * data.spectralProjection 0‖ ≤
          ‖U.evolution t - V.evolution t‖ :=
        leakage_le_comparison _ _ _ _ hP.1 hP.2 hP₀.1 hP₀.2 hinter
      _ ≤ C / T := hbound T hT U V t ht
      _ ≤ (2 * C) / T := div_le_div_of_nonneg_right (by linarith) hT.le

/-- The moving gapped spectral band has a uniform adiabatic leakage bound
for every pair of physical and Kato strong propagators. -/
theorem GappedHamiltonian.exists_adiabatic_bound_of_strong_propagators
    (data : GappedHamiltonian domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ _V : StrongPropagator domain data.H
        (fun t => katoGenerator (data.spectralProjection t)
          (derivWithin data.spectralProjection (Icc (0 : ℝ) 1) t))
        (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(1 - data.spectralProjection t) * U.evolution t * data.spectralProjection 0‖ ≤
          C / T := by
  obtain ⟨L, hL, hcomm⟩ := data.exists_contDiffOn_commutatorLift
  let X : ℝ → E →L[ℂ] E := fun t => domain.inclusion.comp (L t)
  have hX : ContDiffOn ℝ 1 X (Icc (0 : ℝ) 1) :=
    (((ContinuousLinearMap.compL ℂ E D E domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn hL
  have hP := data.spectralProjection_contDiff
  have hdiff := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)
  exact exists_adiabatic_bound_of_strong_commutator domain data.H data.spectralProjection
    (derivWithin data.spectralProjection (Icc (0 : ℝ) 1)) X
    (derivWithin X (Icc (0 : ℝ) 1)) data.spectralProjectionLift L
    (hP.derivWithin hdiff (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuousOn
    hX.continuousOn (hX.continuousOn_derivWithin hdiff (by rfl))
    (fun _ ht => (data.spectralProjection_isStarProjection ht).2)
    (fun _ ht => (data.spectralProjection_isStarProjection ht).1)
    (fun t ht => ((hP.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
    (fun t ht => ((hX.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
    (fun _ ht y => DFunLike.congr_fun (data.inclusion_spectralProjectionLift ht) y)
    (fun _ _ _ => rfl) (fun _ ht => data.spectralProjection_commutes ht) hcomm

end Adiabatic.Unbounded
