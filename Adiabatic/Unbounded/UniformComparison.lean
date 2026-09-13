import Adiabatic.Unbounded.Comparison

/-!
# A runtime-independent comparison bound for strong evolution

Compactness bounds the smooth commutator solution and its derivative before
the runtime is chosen. This gives a uniform operator-norm comparison for
any supplied pair of strong propagators.
-/

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A continuous bounded correction and a continuously differentiable
domain commutator solution give a uniform `C / T` comparison estimate. -/
theorem exists_comparison_bound_of_strong_commutator
    (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)
    (K X dX : ℝ → E →L[ℂ] E) (LX : ℝ → E →L[ℂ] D)
    (hKcont : ContinuousOn K (Icc (0 : ℝ) 1))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) 1))
    (hdXcont : ContinuousOn dX (Icc (0 : ℝ) 1))
    (hXderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hXrange : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, domain.inclusion (LX t y) = X t y)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      H t (LX t (domain.inclusion y)) - X t (H t y) = K t (domain.inclusion y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ V : StrongPropagator domain H K (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, ‖U.evolution t - V.evolution t‖ ≤ C / T := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hXcont
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hdXcont
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hKcont
  have hMn : 0 ≤ M := (norm_nonneg (X 0)).trans (hM 0 (by simp))
  have hNn : 0 ≤ N := (norm_nonneg (dX 0)).trans (hN 0 (by simp))
  have hQn : 0 ≤ Q := (norm_nonneg (K 0)).trans (hQ 0 (by simp))
  refine ⟨2 * M + N + Q * M, by positivity, ?_⟩
  intro T hT U V t ht
  have hz : -Complex.I * (T : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hT.ne')
  calc
    ‖U.evolution t - V.evolution t‖ ≤
        ‖(-Complex.I * (T : ℂ))⁻¹‖ * (2 * M + t * (N + Q * M)) :=
      strong_adiabatic_comparison hz U V X dX LX hXderiv hXrange hcomm
        M N Q hM hN hQ ht
    _ ≤ (1 / T) * (2 * M + (N + Q * M)) := by
      have hinv : ‖(-Complex.I * (T : ℂ))⁻¹‖ = 1 / T := by
        simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, one_div]
      rw [hinv]
      gcongr
      exact mul_le_of_le_one_left (by positivity) ht.2
    _ = (2 * M + N + Q * M) / T := by ring

end Adiabatic.Unbounded
