import Adiabatic.Unbounded.Propagator

/-!
# Exact projection transport for strong unbounded evolution

The Hamiltonian and transport commutators imply exact intertwining.
Differentiation is restricted to a dense domain, and the resulting bounded
operator identity extends to the physical Hilbert space by continuity.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The strong evolution intertwines a differentiable family when the
Hamiltonian commutes with it and the extra generator has commutator `P'`. -/
theorem strong_transport_intertwines
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E}
    {K : ℝ → E →L[ℂ] E} {z : ℂ} (U : StrongPropagator domain H K z)
    (P dP : ℝ → E →L[ℂ] E) (L : ℝ → E →L[ℂ] D)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP t) (Icc 0 1) t)
    (hPrange : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y, domain.inclusion (L t y) = P t y)
    (hHP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y,
      H t (L t (domain.inclusion y)) = P t (H t y))
    (hKP : ∀ t ∈ Icc (0 : ℝ) 1, K t * P t - P t * K t = dP t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    P s * U.evolution s = U.evolution s * P 0 := by
  have hzero (x : D) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt
        (fun a => (star (U.evolution a) * P a * U.evolution a) (domain.inclusion x))
        0 (Icc 0 1) t := by
    have hv := hasDerivWithinAt_apply (hP t ht) (U.strong_derivative x t ht)
    have hw := U.adjoint_strong_derivative (L t (U.evolution t (domain.inclusion x))) ht
    simp only [hPrange t ht] at hw
    have hc := hHP t ht (U.lift t x)
    rw [← U.preserves_domain t ht] at hc
    have hk := congrArg (fun A : E →L[ℂ] E => A (U.evolution t (domain.inclusion x)))
      (hKP t ht)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at hk
    convert hasDerivWithinAt_apply_of_strong
      (A := fun a => star (U.evolution a))
      (v := fun a => P a (U.evolution a (domain.inclusion x)))
      (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ‖star (U.evolution a)‖ ≤ 1 from by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact U.adjoint_norm_le_one ha)
      (U.adjoint_strong_continuous _ t ht) hw hv using 1
    simp only [map_add, map_smul]
    rw [hc, ← hk]
    simp only [map_sub]
    module
  have hprod : star (U.evolution s) * P s * U.evolution s = P 0 := by
    apply ContinuousLinearMap.ext
    have hdense (x : D) :
        (star (U.evolution s) * P s * U.evolution s) (domain.inclusion x) =
          P 0 (domain.inclusion x) := by
      have hc := constant_of_derivWithin_zero
        (fun a ha => (hzero x a ha).differentiableWithinAt)
        (fun a ha => (hzero x a ⟨ha.1, ha.2.le⟩).derivWithin
          (uniqueDiffOn_Icc_zero_one a ⟨ha.1, ha.2.le⟩)) s hs
      simpa only [U.initial, star_one, one_mul, mul_one] using hc
    intro y
    exact congrFun (domain.dense.equalizer
      (star (U.evolution s) * P s * U.evolution s).continuous
      (P 0).continuous (funext hdense)) y
  have heq := congrArg (U.evolution s * ·) hprod
  simpa only [← mul_assoc, Unitary.mul_star_self_of_mem (U.isUnitary s hs), one_mul] using heq

end Adiabatic.Unbounded
