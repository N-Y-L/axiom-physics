import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Bounds for the corrected comparison evolution

A mean-value estimate for the corrected comparison curve gives the
adiabatic error bound.
-/

namespace Adiabatic

open Set

section CorrectedCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A small derivative of `Ω - c • B`, together with a uniform bound on `B`,
controls the change of `Ω` over the unit interval. -/
theorem corrected_curve_bound
    (Ω B R : ℝ → E) (c : ℂ) (M D : ℝ)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => Ω t - c • B t) (-c • R t) (Icc 0 1) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖B t‖ ≤ M)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ ≤ D)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖Ω s - Ω 0‖ ≤ ‖c‖ * (2 * M + s * D) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖-c • R t‖ ≤ ‖c‖ * D := by
    intro t ht
    simpa only [norm_smul, norm_neg] using
      mul_le_mul_of_nonneg_left (hR t ht) (norm_nonneg c)
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hsmall (convex_Icc (0 : ℝ) 1) hzero hs
  have hBdiff : ‖B s - B 0‖ ≤ 2 * M := by
    calc
      ‖B s - B 0‖ ≤ ‖B s‖ + ‖B 0‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hB s hs) (hB 0 hzero)
      _ = 2 * M := by ring
  calc
    ‖Ω s - Ω 0‖ =
        ‖((Ω s - c • B s) - (Ω 0 - c • B 0)) + c • (B s - B 0)‖ := by
      congr 1
      simp only [smul_sub]
      abel
    _ ≤ ‖(Ω s - c • B s) - (Ω 0 - c • B 0)‖ + ‖c • (B s - B 0)‖ :=
      norm_add_le _ _
    _ ≤ (‖c‖ * D) * ‖s - 0‖ + ‖c‖ * (2 * M) := by
      exact add_le_add hmean (by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left hBdiff (norm_nonneg c))
    _ = ‖c‖ * (2 * M + s * D) := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1]
      ring

end CorrectedCurve

section NormedRing

variable {A : Type*} [NormedRing A]

/-- Multiplication on both sides by contractions cannot increase the norm. -/
theorem norm_contraction_mul (a b c : A) (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * b * c‖ ≤ ‖b‖ := by
  calc
    ‖a * b * c‖ ≤ ‖a * b‖ * ‖c‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖) * ‖c‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖b‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) hc
        (norm_nonneg _) (by positivity)
    _ = ‖b‖ := by ring

/-- A uniform bound for the remainder in the commutator argument. -/
theorem norm_commutator_remainder (W U X dX K : A) (M D L : ℝ)
    (hW : ‖W‖ ≤ 1) (hU : ‖U‖ ≤ 1)
    (hX : ‖X‖ ≤ M) (hdX : ‖dX‖ ≤ D) (hK : ‖K‖ ≤ L) :
    ‖W * (dX - K * X) * U‖ ≤ D + L * M := by
  have hL : 0 ≤ L := (norm_nonneg K).trans hK
  calc
    ‖W * (dX - K * X) * U‖ ≤ ‖dX - K * X‖ := norm_contraction_mul _ _ _ hW hU
    _ ≤ ‖dX‖ + ‖K * X‖ := norm_sub_le _ _
    _ ≤ D + ‖K‖ * ‖X‖ := add_le_add hdX (norm_mul_le _ _)
    _ ≤ D + L * M := add_le_add le_rfl (mul_le_mul hK hX (norm_nonneg _) hL)

end NormedRing

end Adiabatic
