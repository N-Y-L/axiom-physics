import Adiabatic.Bounds
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Extending a strong adiabatic estimate from a dense domain

The mean-value argument can be carried out after application to vectors in
a dense domain. Boundedness then extends the resulting inequality to an
operator-norm estimate on the whole Hilbert space. No operator-norm
derivative is used.
-/

namespace Adiabatic.Unbounded

open Set

variable {D E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An operator bound verified on a dense range holds on the whole space. -/
theorem opNorm_le_of_denseRange (j : D → E) (hj : DenseRange j)
    (A : E →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ x, ‖A (j x)‖ ≤ C * ‖j x‖) : ‖A‖ ≤ C := by
  apply A.opNorm_le_bound hC
  intro y
  exact hj.induction_on y
    (isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)) hA

/-- A corrected-curve derivative on a dense domain suffices for the full
operator-norm comparison bound. -/
theorem corrected_curve_bound_of_denseRange
    (j : D → E) (hj : DenseRange j)
    (Ω B R : ℝ → E →L[ℂ] F) (c : ℂ) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hderiv : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun u => Ω u (j x) - c • B u (j x))
        (-c • R t (j x)) (Icc 0 1) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖B t‖ ≤ M)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ ≤ N)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖Ω s - Ω 0‖ ≤ ‖c‖ * (2 * M + s * N) := by
  apply opNorm_le_of_denseRange j hj _ (mul_nonneg (norm_nonneg c) (add_nonneg (mul_nonneg (by norm_num) hM) (mul_nonneg hs.1 hN)))
  intro x
  have h := corrected_curve_bound
    (fun u => Ω u (j x)) (fun u => B u (j x)) (fun u => R u (j x))
    c (M * ‖j x‖) (N * ‖j x‖) (hderiv x)
    (fun t ht => ((B t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hB t ht) (norm_nonneg _)))
    (fun t ht => ((R t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hR t ht) (norm_nonneg _))) hs
  convert h using 1
  ring

end Adiabatic.Unbounded
