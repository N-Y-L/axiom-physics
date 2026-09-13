import Adiabatic.Unbounded.StrongCalculus
import Adiabatic.Evolution

/-!
# The commutator argument on a common domain

These differential identities allow genuinely unbounded Hamiltonians:
`H : D →L[ℂ] E` acts on a separate domain, included by `j : D →L[ℂ] E`.
The evolution equations are strong vector derivatives. The commutator
solution is bounded on the physical space and maps it into the domain.
No operator-norm derivative of either evolution is assumed.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {j : D →L[ℂ] E} {z : ℂ} {W U X : ℝ → E →L[ℂ] E}
  {H : D →L[ℂ] E} {K dX : E →L[ℂ] E} {s : Set ℝ} {t M : ℝ}

/-- Cancellation of the two Hamiltonian terms in the strong wave derivative. -/
theorem hasDerivWithinAt_waveOperator_apply (x u : D)
    (hWbound : ∀ᶠ a in 𝓝[s] t, ‖W a‖ ≤ M)
    (hWcont : ∀ y, ContinuousWithinAt (fun a => W a y) s t)
    (hUdom : U t (j x) = j u)
    (hU : HasDerivWithinAt (fun a => U a (j x)) (z • H u) s t)
    (hW : ∀ y, HasDerivWithinAt (fun a => W a (j y))
      (-(z • W t (H y)) - W t (K (j y))) s t) :
    HasDerivWithinAt (fun a => waveOperator W U a (j x))
      (-(W t * K * U t) (j x)) s t := by
  have hw : HasDerivWithinAt (fun a => W a (U t (j x)))
      (-(z • W t (H u)) - W t (K (j u))) s t := by
    simpa only [hUdom] using hW u
  convert hasDerivWithinAt_apply_of_strong hWbound (hWcont _) hw hU using 1
  simp only [ContinuousLinearMap.mul_apply, map_smul, hUdom]
  module

/-- Differentiation of the transported commutator on a domain vector. -/
theorem hasDerivWithinAt_transportedCommutator_apply (x u : D) (L : E →L[ℂ] D)
    (hWbound : ∀ᶠ a in 𝓝[s] t, ‖W a‖ ≤ M)
    (hWcont : ∀ y, ContinuousWithinAt (fun a => W a y) s t)
    (hUdom : U t (j x) = j u)
    (hU : HasDerivWithinAt (fun a => U a (j x)) (z • H u) s t)
    (hW : ∀ y, HasDerivWithinAt (fun a => W a (j y))
      (-(z • W t (H y)) - W t (K (j y))) s t)
    (hX : HasDerivWithinAt X dX s t)
    (hXrange : ∀ y, j (L y) = X t y)
    (hcomm : ∀ y, H (L (j y)) - X t (H y) = K (j y)) :
    HasDerivWithinAt (fun a => transportedCommutator W X U a (j x))
      (-(z • (W t * K * U t) (j x)) +
        (W t * (dX - K * X t) * U t) (j x)) s t := by
  have hv := hasDerivWithinAt_apply hX hU
  have hw := hW (L (U t (j x)))
  simp only [hXrange] at hw
  have hc := hcomm u
  rw [← hUdom] at hc
  convert hasDerivWithinAt_apply_of_strong hWbound (hWcont _) hw hv using 1
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, map_smul, map_add, map_sub]
  rw [← hc]
  simp only [map_sub]
  module

/-- The corrected strong derivative is proportional to the inverse runtime. -/
theorem hasDerivWithinAt_correctedEvolution_apply (hz : z ≠ 0)
    (x u : D) (L : E →L[ℂ] D)
    (hWbound : ∀ᶠ a in 𝓝[s] t, ‖W a‖ ≤ M)
    (hWcont : ∀ y, ContinuousWithinAt (fun a => W a y) s t)
    (hUdom : U t (j x) = j u)
    (hU : HasDerivWithinAt (fun a => U a (j x)) (z • H u) s t)
    (hW : ∀ y, HasDerivWithinAt (fun a => W a (j y))
      (-(z • W t (H y)) - W t (K (j y))) s t)
    (hX : HasDerivWithinAt X dX s t)
    (hXrange : ∀ y, j (L y) = X t y)
    (hcomm : ∀ y, H (L (j y)) - X t (H y) = K (j y)) :
    HasDerivWithinAt (fun a => correctedEvolution z W X U a (j x))
      (-(z⁻¹ • (W t * (dX - K * X t) * U t) (j x))) s t := by
  have hΩ := hasDerivWithinAt_waveOperator_apply x u hWbound hWcont hUdom hU hW
  have hB := hasDerivWithinAt_transportedCommutator_apply x u L
    hWbound hWcont hUdom hU hW hX hXrange hcomm
  convert hΩ.sub (hB.const_smul z⁻¹) using 1
  simp only [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hz, one_smul]
  module

end Adiabatic.Unbounded
