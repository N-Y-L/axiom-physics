import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Differential identities for adiabatic comparison

These identities follow from the evolution equations and the commutator
equation. They do not assume an error estimate. The parameter `z` specializes
to `-Complex.I * T` for the physical Schrödinger equation. The path `W` then
represents the adjoint of the adiabatic evolution.
-/

namespace Adiabatic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The wave operator comparing the physical and adiabatic evolutions. -/
def waveOperator (W U : ℝ → A) (t : ℝ) : A := W t * U t

/-- The commutator solution transported between the two evolutions. -/
def transportedCommutator (W X U : ℝ → A) (t : ℝ) : A := W t * X t * U t

/-- The wave operator with its rapidly varying derivative canceled. -/
noncomputable def correctedEvolution (z : ℂ) (W X U : ℝ → A) (t : ℝ) : A :=
  waveOperator W U t - z⁻¹ • transportedCommutator W X U t

/-- The Hamiltonian terms cancel in the derivative of the wave operator. -/
theorem hasDerivAt_waveOperator {z : ℂ} {W U : ℝ → A} {H K : A} {t : ℝ}
    (hU : HasDerivAt U (z • (H * U t)) t)
    (hW : HasDerivAt W (-(z • (W t * H)) - W t * K) t) :
    HasDerivAt (waveOperator W U) (-(W t * K * U t)) t := by
  convert hW.mul hU using 1
  simp only [sub_mul, neg_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  module

/-- Differentiating the transported commutator isolates the large parameter. -/
theorem hasDerivAt_transportedCommutator {z : ℂ} {W X U : ℝ → A}
    {H K dX : A} {t : ℝ}
    (hU : HasDerivAt U (z • (H * U t)) t)
    (hW : HasDerivAt W (-(z • (W t * H)) - W t * K) t)
    (hX : HasDerivAt X dX t)
    (hcomm : H * X t - X t * H = K) :
    HasDerivAt (transportedCommutator W X U)
      (-(z • (W t * K * U t)) + W t * (dX - K * X t) * U t) t := by
  convert (hW.mul hX).mul hU using 1
  rw [← hcomm]
  simp only [Pi.mul_apply, sub_mul, mul_sub, add_mul, neg_mul, smul_mul_assoc,
    mul_smul_comm, mul_assoc, smul_sub]
  module

/-- The corrected curve has a derivative proportional to the inverse runtime. -/
theorem hasDerivAt_correctedEvolution {z : ℂ} (hz : z ≠ 0) {W X U : ℝ → A}
    {H K dX : A} {t : ℝ}
    (hU : HasDerivAt U (z • (H * U t)) t)
    (hW : HasDerivAt W (-(z • (W t * H)) - W t * K) t)
    (hX : HasDerivAt X dX t)
    (hcomm : H * X t - X t * H = K) :
    HasDerivAt (correctedEvolution z W X U)
      (-(z⁻¹ • (W t * (dX - K * X t) * U t))) t := by
  have hΩ := hasDerivAt_waveOperator hU hW
  have hB := hasDerivAt_transportedCommutator hU hW hX hcomm
  convert hΩ.sub (hB.const_smul z⁻¹) using 1
  simp only [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hz, one_smul]
  module

/-- Within-set wave differentiation, including interval endpoints. -/
theorem hasDerivWithinAt_waveOperator {z : ℂ} {W U : ℝ → A} {H K : A}
    {s : Set ℝ} {t : ℝ}
    (hU : HasDerivWithinAt U (z • (H * U t)) s t)
    (hW : HasDerivWithinAt W (-(z • (W t * H)) - W t * K) s t) :
    HasDerivWithinAt (waveOperator W U) (-(W t * K * U t)) s t := by
  convert hW.mul hU using 1
  simp only [sub_mul, neg_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  module

/-- The transported-commutator derivative with derivatives within a set. -/
theorem hasDerivWithinAt_transportedCommutator {z : ℂ} {W X U : ℝ → A}
    {H K dX : A} {s : Set ℝ} {t : ℝ}
    (hU : HasDerivWithinAt U (z • (H * U t)) s t)
    (hW : HasDerivWithinAt W (-(z • (W t * H)) - W t * K) s t)
    (hX : HasDerivWithinAt X dX s t)
    (hcomm : H * X t - X t * H = K) :
    HasDerivWithinAt (transportedCommutator W X U)
      (-(z • (W t * K * U t)) + W t * (dX - K * X t) * U t) s t := by
  convert (hW.mul hX).mul hU using 1
  rw [← hcomm]
  simp only [Pi.mul_apply, sub_mul, mul_sub, add_mul, neg_mul, smul_mul_assoc,
    mul_smul_comm, mul_assoc, smul_sub]
  module

/-- The inverse-runtime corrected derivative with derivatives within a set. -/
theorem hasDerivWithinAt_correctedEvolution {z : ℂ} (hz : z ≠ 0)
    {W X U : ℝ → A} {H K dX : A} {s : Set ℝ} {t : ℝ}
    (hU : HasDerivWithinAt U (z • (H * U t)) s t)
    (hW : HasDerivWithinAt W (-(z • (W t * H)) - W t * K) s t)
    (hX : HasDerivWithinAt X dX s t)
    (hcomm : H * X t - X t * H = K) :
    HasDerivWithinAt (correctedEvolution z W X U)
      (-(z⁻¹ • (W t * (dX - K * X t) * U t))) s t := by
  have hΩ := hasDerivWithinAt_waveOperator hU hW
  have hB := hasDerivWithinAt_transportedCommutator hU hW hX hcomm
  convert hΩ.sub (hB.const_smul z⁻¹) using 1
  simp only [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hz, one_smul]
  module

section Adjoint

variable [StarRing A] [NormedStarGroup A] [StarModule ℂ A]

/-- The adjoint of adiabatic Schrödinger evolution satisfies the equation
used in the comparison identities. Time derivatives here are real. -/
theorem hasDerivAt_adjointEvolution {z : ℂ} {V : ℝ → A} {H K : A} {t : ℝ}
    (hz : star z = -z) (hH : star H = H) (hK : star K = -K)
    (hV : HasDerivAt V (z • (H * V t) + K * V t) t) :
    HasDerivAt (fun s => star (V s))
      (-(z • (star (V t) * H)) - star (V t) * K) t := by
  convert hV.star using 1
  simp only [star_add, star_smul, star_mul, hz, hH, hK, neg_smul, mul_neg,
    sub_eq_add_neg]

/-- The adjoint evolution equation with derivatives within a set. -/
theorem hasDerivWithinAt_adjointEvolution {z : ℂ} {V : ℝ → A} {H K : A}
    {s : Set ℝ} {t : ℝ}
    (hz : star z = -z) (hH : star H = H) (hK : star K = -K)
    (hV : HasDerivWithinAt V (z • (H * V t) + K * V t) s t) :
    HasDerivWithinAt (fun u => star (V u))
      (-(z • (star (V t) * H)) - star (V t) * K) s t := by
  convert hV.star using 1
  simp only [star_add, star_smul, star_mul, hz, hH, hK, neg_smul, mul_neg,
    sub_eq_add_neg]

end Adjoint

end Adiabatic
