import Adiabatic.Bounds
import Adiabatic.Evolution
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Conditional adiabatic comparison

The comparison bound follows from the two evolution equations and a bounded,
differentiable solution of `[H,X] = K`. Construction of that solution from a
spectral gap is a separate step. The evolutions are supplied as unitary paths.
-/

namespace Adiabatic

open Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [StarRing A] [CStarRing A] [StarModule ℂ A]
  [Nontrivial A]

/-- A quantitative comparison derived from evolution equations.
`X`, `dX`, `K`, and their bounds must be fixed independently of `z` when this
theorem is used for a family of runtimes. -/
theorem adiabatic_comparison
    (H K X dX U V : ℝ → A) (z : ℂ) (M D L : ℝ)
    (hz : z ≠ 0) (hzstar : star z = -z)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, star (K t) = -K t)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt U (z • (H t * U t)) (Icc 0 1) t)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V (z • (H t * V t) + K t * V t) (Icc 0 1) t)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1, H t * X t - X t * H t = K t)
    (hUunitary : ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary A)
    (hVunitary : ∀ t ∈ Icc (0 : ℝ) 1, V t ∈ unitary A)
    (hUzero : U 0 = 1) (hVzero : V 0 = 1)
    (hMX : ∀ t ∈ Icc (0 : ℝ) 1, ‖X t‖ ≤ M)
    (hDX : ∀ t ∈ Icc (0 : ℝ) 1, ‖dX t‖ ≤ D)
    (hLK : ∀ t ∈ Icc (0 : ℝ) 1, ‖K t‖ ≤ L)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖U s - V s‖ ≤ ‖z⁻¹‖ * (2 * M + s * (D + L * M)) := by
  let W : ℝ → A := fun t => star (V t)
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt W (-(z • (W t * H t)) - W t * K t) (Icc 0 1) t :=
    hasDerivWithinAt_adjointEvolution hzstar (hH t ht) (hK t ht) (hV t ht)
  have hnW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖W t‖ ≤ 1 := by
    dsimp [W]
    rw [norm_star, CStarRing.norm_of_mem_unitary (hVunitary t ht)]
  have hnU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖U t‖ ≤ 1 := by
    rw [CStarRing.norm_of_mem_unitary (hUunitary t ht)]
  have hcorrected := corrected_curve_bound
    (waveOperator W U) (transportedCommutator W X U)
    (fun t => W t * (dX t - K t * X t) * U t) z⁻¹ M (D + L * M)
    (fun t ht => by
      simpa only [correctedEvolution, neg_smul] using
        (hasDerivWithinAt_correctedEvolution hz (hU t ht) (hW t ht)
          (hX t ht) (hcomm t ht)))
    (fun t ht => (norm_contraction_mul _ _ _ (hnW t ht) (hnU t ht)).trans (hMX t ht))
    (fun t ht => norm_commutator_remainder _ _ _ _ _ M D L
      (hnW t ht) (hnU t ht) (hMX t ht) (hDX t ht) (hLK t ht)) hs
  have hnorm : ‖waveOperator W U s - waveOperator W U 0‖ = ‖U s - V s‖ := by
    dsimp [waveOperator, W]
    rw [hUzero, hVzero, star_one, one_mul,
      ← Unitary.star_mul_self_of_mem (hVunitary s hs), ← mul_sub]
    exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (hVunitary s hs))
  rwa [hnorm] at hcorrected

end Adiabatic
