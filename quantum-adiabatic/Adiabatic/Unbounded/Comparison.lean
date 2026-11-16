import Adiabatic.Unbounded.Propagator
import Adiabatic.Unbounded.Evolution
import Adiabatic.Unbounded.StrongEstimate
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Adiabatic comparison for supplied unbounded strong propagators

The quantitative estimate follows from the strong equations on a dense
common domain. The propagators and a differentiable commutator solution
are inputs at this stage; their construction is a separate dependency.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The full operator-norm comparison estimate derived from strong equations
on a dense domain. The bounds on `X`, `dX`, and `K` must be independent of the
runtime when this theorem is used for an adiabatic family. -/
theorem strong_adiabatic_comparison
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E}
    {K : ℝ → E →L[ℂ] E} {z : ℂ} (hz : z ≠ 0)
    (U : StrongPropagator domain H (fun _ => 0) z)
    (V : StrongPropagator domain H K z)
    (X dX : ℝ → E →L[ℂ] E) (L : ℝ → E →L[ℂ] D)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hXrange : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, domain.inclusion (L t y) = X t y)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      H t (L t (domain.inclusion y)) - X t (H t y) = K t (domain.inclusion y))
    (M N Q : ℝ)
    (hMX : ∀ t ∈ Icc (0 : ℝ) 1, ‖X t‖ ≤ M)
    (hNX : ∀ t ∈ Icc (0 : ℝ) 1, ‖dX t‖ ≤ N)
    (hQK : ∀ t ∈ Icc (0 : ℝ) 1, ‖K t‖ ≤ Q)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖U.evolution s - V.evolution s‖ ≤ ‖z⁻¹‖ * (2 * M + s * (N + Q * M)) := by
  let W := fun t => star (V.evolution t)
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMX 0 hzero)
  have hN : 0 ≤ N := (norm_nonneg _).trans (hNX 0 hzero)
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (hQK 0 hzero)
  have hcorrected := corrected_curve_bound_of_denseRange domain.inclusion domain.dense
    (waveOperator W U.evolution) (transportedCommutator W X U.evolution)
    (fun t => W t * (dX t - K t * X t) * U.evolution t)
    z⁻¹ hM (add_nonneg hN (mul_nonneg hQ hM))
    (fun x t ht => by
      have hd := hasDerivWithinAt_correctedEvolution_apply hz x (U.lift t x) (L t)
        (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ‖W a‖ ≤ 1 from by
          filter_upwards [self_mem_nhdsWithin] with a ha
          exact V.adjoint_norm_le_one ha)
        (fun y => V.adjoint_strong_continuous y t ht)
        (U.preserves_domain t ht x)
        (show HasDerivWithinAt (fun a => U.evolution a (domain.inclusion x))
          (z • H t (U.lift t x)) (Icc 0 1) t from by
          simpa using U.strong_derivative x t ht)
        (fun y => V.adjoint_strong_derivative y ht)
        (hX t ht) (hXrange t ht) (hcomm t ht)
      simpa only [correctedEvolution, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, neg_smul] using hd)
    (fun t ht => (norm_contraction_mul _ _ _
      (V.adjoint_norm_le_one ht) (U.norm_le_one ht)).trans (hMX t ht))
    (fun t ht => norm_commutator_remainder _ _ _ _ _ M N Q
      (V.adjoint_norm_le_one ht) (U.norm_le_one ht) (hMX t ht) (hNX t ht) (hQK t ht)) hs
  have hn : ‖waveOperator W U.evolution s - waveOperator W U.evolution 0‖ =
      ‖U.evolution s - V.evolution s‖ := by
    dsimp [waveOperator, W]
    rw [U.initial, V.initial, star_one, one_mul,
      ← Unitary.star_mul_self_of_mem (V.isUnitary s hs), ← mul_sub]
    exact CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (V.isUnitary s hs))
  rwa [hn] at hcorrected

end Adiabatic.Unbounded
