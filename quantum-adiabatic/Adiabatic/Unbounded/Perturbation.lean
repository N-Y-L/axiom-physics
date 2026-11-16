import Adiabatic.Unbounded.Propagator

/-!
# Comparing strong evolutions with different Hamiltonians

This Duhamel estimate measures Hamiltonian differences from the common
domain to the physical Hilbert space. It does not take the operator norm
of an unbounded Hamiltonian on the physical space. It is suited to
comparison of frozen Hamiltonians in a time-slicing construction.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Uniform Hamiltonian error and a domain propagation bound control the
evolution error on the domain. -/
theorem strong_propagator_perturbation
    {domain : CommonDomain D E} {H₁ H₂ : ℝ → D →L[ℂ] E} {z : ℂ}
    (U : StrongPropagator domain H₁ (fun _ => 0) z)
    (V : StrongPropagator domain H₂ (fun _ => 0) z)
    {ε B : ℝ}
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ‖H₁ t - H₂ t‖ ≤ ε)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖U.lift t‖ ≤ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(U.evolution s - V.evolution s).comp domain.inclusion‖ ≤ s * ‖z‖ * ε * B := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hH 0 hzero)
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0 hzero)
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg hs.1 (norm_nonneg z)) hε) hBn)
  intro x
  let f := fun t => star (V.evolution t) (U.evolution t (domain.inclusion x))
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt f
        (z • star (V.evolution t) ((H₁ t - H₂ t) (U.lift t x))) (Icc 0 1) t := by
    have hw := V.adjoint_strong_derivative (U.lift t x) ht
    rw [← U.preserves_domain t ht] at hw
    have hu := U.strong_derivative x t ht
    simp only [ContinuousLinearMap.zero_apply, add_zero] at hu hw
    convert hasDerivWithinAt_apply_of_strong
      (A := fun a => star (V.evolution a))
      (v := fun a => U.evolution a (domain.inclusion x))
      (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ‖star (V.evolution a)‖ ≤ 1 from by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact V.adjoint_norm_le_one ha)
      (V.adjoint_strong_continuous _ t ht) hw hu using 1
    simp only [ContinuousLinearMap.sub_apply, map_smul, map_sub, map_zero, sub_zero, smul_sub]
    module
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖z • star (V.evolution t) ((H₁ t - H₂ t) (U.lift t x))‖ ≤
        ‖z‖ * ε * B * ‖x‖ := by
    rw [norm_smul, ContinuousLinearMap.norm_map_of_mem_unitary
      (Unitary.star_mem (V.isUnitary t ht))]
    calc
      ‖z‖ * ‖(H₁ t - H₂ t) (U.lift t x)‖ ≤
          ‖z‖ * (‖H₁ t - H₂ t‖ * ‖U.lift t x‖) := by
        gcongr
        exact (H₁ t - H₂ t).le_opNorm _
      _ ≤ ‖z‖ * (ε * (B * ‖x‖)) := by
        gcongr
        · exact hH t ht
        · exact ((U.lift t).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hB t ht) (norm_nonneg x))
      _ = ‖z‖ * ε * B * ‖x‖ := by ring
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hf hbound (convex_Icc (0 : ℝ) 1) hzero hs
  have heq : f s - f 0 = star (V.evolution s)
      ((U.evolution s - V.evolution s) (domain.inclusion x)) := by
    dsimp [f]
    rw [U.initial, V.initial, star_one, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.one_apply, map_sub]
    congr 1
    exact (congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
      (Unitary.star_mul_self_of_mem (V.isUnitary s hs))).symm
  rw [heq, ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.star_mem (V.isUnitary s hs))] at hmean
  convert hmean using 1
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1]
  ring

end Adiabatic.Unbounded
