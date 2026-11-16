import Adiabatic.Unbounded.Comparison
import Adiabatic.Unbounded.Transport
import Adiabatic.Leakage

/-!
# Uniform unbounded adiabatic estimate from strong propagators

The constant is chosen before the runtime, using compactness and the
commutator solution. This theorem permits unbounded Hamiltonians.
The physical and Kato propagators, spectral projection, and commutator
solution are supplied as hypotheses.
-/

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Strong common-domain evolution and a C¹ commutator solution imply
a runtime-independent `C / T` bound for leakage. -/
theorem exists_adiabatic_bound_of_strong_commutator
    (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)
    (P dP X dX : ℝ → E →L[ℂ] E) (LP LX : ℝ → E →L[ℂ] D)
    (hdPcont : ContinuousOn dP (Icc (0 : ℝ) 1))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) 1))
    (hdXcont : ContinuousOn dX (Icc (0 : ℝ) 1))
    (hPstar : ∀ t ∈ Icc (0 : ℝ) 1, star (P t) = P t)
    (hPid : ∀ t ∈ Icc (0 : ℝ) 1, P t * P t = P t)
    (hPderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP t) (Icc 0 1) t)
    (hXderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hPrange : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, domain.inclusion (LP t y) = P t y)
    (hXrange : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, domain.inclusion (LX t y) = X t y)
    (hHP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      H t (LP t (domain.inclusion y)) = P t (H t y))
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      H t (LX t (domain.inclusion y)) - X t (H t y) =
        katoGenerator (P t) (dP t) (domain.inclusion y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ _V : StrongPropagator domain H (fun t => katoGenerator (P t) (dP t))
        (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(1 - P t) * U.evolution t * P 0‖ ≤ C / T := by
  let K := fun t => katoGenerator (P t) (dP t)
  have hPcont : ContinuousOn P (Icc (0 : ℝ) 1) :=
    fun t ht => (hPderiv t ht).continuousWithinAt
  have hKcont : ContinuousOn K (Icc (0 : ℝ) 1) :=
    (hdPcont.mul hPcont).sub (hPcont.mul hdPcont)
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
  have hinter : P t * V.evolution t = V.evolution t * P 0 :=
    strong_transport_intertwines V P dP LP hPderiv hPrange hHP
      (fun a ha => katoGenerator_commutator_of_hasDerivWithinAt
        hPid ha (uniqueDiffOn_Icc_zero_one a ha) (hPderiv a ha)) ht
  have hc := strong_adiabatic_comparison hz U V X dX LX hXderiv hXrange hcomm
    M N Q hM hN hQ ht
  calc
    ‖(1 - P t) * U.evolution t * P 0‖ ≤ ‖U.evolution t - V.evolution t‖ :=
      leakage_le_comparison _ _ _ _ (hPid t ht) (hPstar t ht)
        (hPid 0 (by simp)) (hPstar 0 (by simp)) hinter
    _ ≤ ‖(-Complex.I * (T : ℂ))⁻¹‖ * (2 * M + t * (N + Q * M)) := hc
    _ ≤ (1 / T) * (2 * M + (N + Q * M)) := by
      have hinv : ‖(-Complex.I * (T : ℂ))⁻¹‖ = 1 / T := by
        simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, one_div]
      rw [hinv]
      gcongr
      exact mul_le_of_le_one_left (by positivity) ht.2
    _ = (2 * M + N + Q * M) / T := by ring

end Adiabatic.Unbounded
