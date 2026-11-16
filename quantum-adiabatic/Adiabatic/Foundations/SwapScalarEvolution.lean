import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Scalar evolution used by the constant-swap obstruction

An integrating factor identifies every scalar strong solution on the closed
unit interval. This is the analytic uniqueness step needed when the two
coordinates of a proposed common-domain swap evolution are inspected.
-/

namespace Adiabatic.Foundations

open Set

/-- The integrating factor is constant for a scalar autonomous equation. -/
theorem scalar_integrating_factor (f : ℝ → ℂ) (c : ℂ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt f (c * f t) (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Complex.exp (-(t : ℂ) * c) * f t = f 0 := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r : ℝ => Complex.exp (-(r : ℂ) * c) * f r)
        0 (Icc 0 1) s := by
    have he := (((hasDerivAt_id s).ofReal_comp.neg.mul_const c).cexp).hasDerivWithinAt
      (s := Icc (0 : ℝ) 1)
    convert he.mul (hf s hs) using 1
    simp
    ring
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun s hs => (le_refl (‖(0 : ℂ)‖))) (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ht
  have heq : Complex.exp (-(t : ℂ) * c) * f t -
      Complex.exp (-(0 : ℂ) * c) * f 0 = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa using hbound) (norm_nonneg _))
  simpa using sub_eq_zero.mp heq

/-- Every solution of the swap's two coordinate equations transfers the first
coordinate to the second at runtime `π / 2` and time one. No domain lift for
the explicit comparison curve is assumed. -/
theorem swap_quarter_turn_coordinates (f g : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt f ((-Complex.I * (Real.pi / 2 : ℝ)) * g t) (Icc 0 1) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((-Complex.I * (Real.pi / 2 : ℝ)) * f t) (Icc 0 1) t)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) : f 1 = 0 ∧ g 1 = -Complex.I := by
  let c : ℂ := -Complex.I * (Real.pi / 2 : ℝ)
  have hp := scalar_integrating_factor (fun t => f t + g t) c
    (fun t ht => by
      convert (hf t ht).add (hg t ht) using 1
      dsimp [c]
      ring)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hm := scalar_integrating_factor (fun t => f t - g t) (-c)
    (fun t ht => by
      convert (hf t ht).sub (hg t ht) using 1
      dsimp [c]
      ring)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hep : Complex.exp (-c) = Complex.I := by
    have hc : -c = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by dsimp [c]; ring
    rw [hc, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  have hem : Complex.exp c = -Complex.I := by
    rw [← neg_neg c, Complex.exp_neg, hep]
    simp
  simp only [Complex.ofReal_one, neg_mul, one_mul, hf0, hg0, add_zero, sub_zero] at hp hm
  rw [hep] at hp
  simp only [neg_neg] at hm
  rw [hem] at hm
  have hplus : f 1 + g 1 = -Complex.I := by
    calc
      f 1 + g 1 = -Complex.I * (Complex.I * (f 1 + g 1)) := by simp [← mul_assoc]
      _ = -Complex.I := by rw [hp]; simp
  have hminus : f 1 - g 1 = Complex.I := by
    calc
      f 1 - g 1 = Complex.I * (-Complex.I * (f 1 - g 1)) := by simp [← mul_assoc]
      _ = Complex.I := by rw [hm]; simp
  constructor
  · linear_combination (hplus + hminus) / 2
  · linear_combination (hplus - hminus) / 2

end Adiabatic.Foundations
