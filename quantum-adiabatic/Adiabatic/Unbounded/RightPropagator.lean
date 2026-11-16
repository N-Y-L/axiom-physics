import Adiabatic.Unbounded.Propagator

/-!
# Right strong propagators and their comparison

Frozen Hamiltonians produce evolutions with right derivatives at the time
partition points. Comparing such evolutions directly avoids any need for
matching partitions. The Hamiltonian error is measured from the common
domain to the physical Hilbert space.
-/

namespace Adiabatic.Unbounded

open Set Filter
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Unitary domain-preserving evolution with a right strong derivative.
This allows jumps in a piecewise frozen Hamiltonian. -/
structure RightStrongPropagator (domain : CommonDomain D E)
    (H : ℝ → D →L[ℂ] E) (z : ℂ) where
  evolution : ℝ → E →L[ℂ] E
  lift : ℝ → D →L[ℂ] D
  inverseLift : ℝ → D →L[ℂ] D
  initial : evolution 0 = 1
  isUnitary : ∀ t ∈ Icc (0 : ℝ) 1, evolution t ∈ unitary (E →L[ℂ] E)
  preserves_domain : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    evolution t (domain.inclusion x) = domain.inclusion (lift t x)
  inverse_preserves_domain : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    star (evolution t) (domain.inclusion x) = domain.inclusion (inverseLift t x)
  strong_continuous : ∀ x, ContinuousOn (fun t => evolution t x) (Icc (0 : ℝ) 1)
  domain_continuous : ∀ x, ContinuousOn (fun t => lift t x) (Icc (0 : ℝ) 1)
  strong_right_derivative : ∀ x, ∀ t ∈ Ico (0 : ℝ) 1,
    HasDerivWithinAt (fun a => evolution a (domain.inclusion x))
      (z • H t (lift t x)) (Ici t) t

/-- A point before the right endpoint has a right neighborhood in the
closed unit interval. -/
theorem unitInterval_mem_nhdsWithin_right {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Icc (0 : ℝ) 1 ∈ 𝓝[Ici t] t := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with u hu hu1
  exact ⟨ht.1.trans hu, hu1.le⟩

namespace RightStrongPropagator

variable {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {z : ℂ}
  (U : RightStrongPropagator domain H z)

/-- Right strong evolution is a physical-space contraction. -/
theorem norm_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖U.evolution t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary (U.isUnitary t ht)]

/-- Inverse evolutions have the same physical norm bound. -/
theorem adjoint_norm_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖star (U.evolution t)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (U.isUnitary t ht))]

/-- Strong continuity passes to the inverse of a right evolution. -/
theorem adjoint_strong_continuous (x : E) :
    ContinuousOn (fun t => star (U.evolution t) x) (Icc (0 : ℝ) 1) := by
  intro t ht
  apply continuousWithinAt_inverse_apply_of_strong (A := U.evolution) (M := 1)
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact U.adjoint_norm_le_one hu
  · filter_upwards [self_mem_nhdsWithin] with u hu
    intro y
    exact congrArg (fun A : E →L[ℂ] E => A y)
      (Unitary.star_mul_self_of_mem (U.isUnitary u hu))
  · exact congrArg (fun A : E →L[ℂ] E => A x)
      (Unitary.mul_star_self_of_mem (U.isUnitary t ht))
  · exact U.strong_continuous _ t ht

/-- Domain lifts cancel in the forward and inverse directions. -/
theorem lift_inverseLift {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    U.lift t (U.inverseLift t x) = x := by
  apply domain.injective
  rw [← U.preserves_domain t ht, ← U.inverse_preserves_domain t ht]
  exact congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
    (Unitary.mul_star_self_of_mem (U.isUnitary t ht))

/-- The adjoint has the inverse right strong derivative, including at time
partition points where the frozen Hamiltonian changes. -/
theorem adjoint_strong_right_derivative (x : D) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (fun u => star (U.evolution u) (domain.inclusion x))
      (-(z • star (U.evolution t) (H t x))) (Ici t) t := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hnear := unitInterval_mem_nhdsWithin_right ht
  have hV : HasDerivWithinAt
      (fun u => U.evolution u (star (U.evolution t) (domain.inclusion x))) (z • H t x) (Ici t) t := by
    rw [U.inverse_preserves_domain t ht']
    simpa only [U.lift_inverseLift ht'] using U.strong_right_derivative (U.inverseLift t x) t ht
  have hd := hasDerivWithinAt_inverse_apply_of_strong
    (A := U.evolution) (B := fun u => star (U.evolution u)) (M := 1)
    (show ∀ᶠ u in 𝓝[Ici t] t, ‖star (U.evolution u)‖ ≤ 1 from by
      filter_upwards [hnear] with u hu; exact U.adjoint_norm_le_one hu)
    (show ∀ᶠ u in 𝓝[Ici t] t, ∀ y, star (U.evolution u) (U.evolution u y) = y from by
      filter_upwards [hnear] with u hu
      intro y
      exact congrArg (fun A : E →L[ℂ] E => A y)
        (Unitary.star_mul_self_of_mem (U.isUnitary u hu)))
    (congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
      (Unitary.mul_star_self_of_mem (U.isUnitary t ht')))
    ((U.adjoint_strong_continuous _ t ht').mono_of_mem_nhdsWithin hnear) hV
  simpa only [map_smul] using hd

end RightStrongPropagator

/-- A Duhamel estimate for right strong evolutions, allowing different
partitions of their piecewise frozen Hamiltonians. -/
theorem right_strong_propagator_perturbation
    {domain : CommonDomain D E} {H₁ H₂ : ℝ → D →L[ℂ] E} {z : ℂ}
    (U : RightStrongPropagator domain H₁ z) (V : RightStrongPropagator domain H₂ z)
    {ε B : ℝ}
    (hH : ∀ t ∈ Ico (0 : ℝ) 1, ‖H₁ t - H₂ t‖ ≤ ε)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖U.lift t‖ ≤ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(U.evolution s - V.evolution s).comp domain.inclusion‖ ≤ s * ‖z‖ * ε * B := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hH 0 (by simp))
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0 hzero)
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg hs.1 (norm_nonneg z)) hε) hBn)
  intro x
  let f := fun t => star (V.evolution t) (U.evolution t (domain.inclusion x))
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro t ht
    apply tendsto_apply_of_strong (M := 1)
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact V.adjoint_norm_le_one hu
    · exact V.adjoint_strong_continuous _ t ht
    · exact U.strong_continuous _ t ht
  have hf (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      HasDerivWithinAt f
        (z • star (V.evolution t) ((H₁ t - H₂ t) (U.lift t x))) (Ici t) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hnear := unitInterval_mem_nhdsWithin_right ht
    have hw := V.adjoint_strong_right_derivative (U.lift t x) ht
    rw [← U.preserves_domain t ht'] at hw
    have hu := U.strong_right_derivative x t ht
    convert hasDerivWithinAt_apply_of_strong
      (A := fun a => star (V.evolution a)) (v := fun a => U.evolution a (domain.inclusion x))
      (show ∀ᶠ a in 𝓝[Ici t] t, ‖star (V.evolution a)‖ ≤ 1 from by
        filter_upwards [hnear] with a ha; exact V.adjoint_norm_le_one ha)
      ((V.adjoint_strong_continuous _ t ht').mono_of_mem_nhdsWithin hnear) hw hu using 1
    simp only [ContinuousLinearMap.sub_apply, map_smul, map_sub, smul_sub]
    module
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖z • star (V.evolution t) ((H₁ t - H₂ t) (U.lift t x))‖ ≤ ‖z‖ * ε * B * ‖x‖ := by
    rw [norm_smul, ContinuousLinearMap.norm_map_of_mem_unitary
      (Unitary.star_mem (V.isUnitary t ⟨ht.1, ht.2.le⟩))]
    calc
      ‖z‖ * ‖(H₁ t - H₂ t) (U.lift t x)‖ ≤
          ‖z‖ * (‖H₁ t - H₂ t‖ * ‖U.lift t x‖) := by
        gcongr; exact (H₁ t - H₂ t).le_opNorm _
      _ ≤ ‖z‖ * (ε * (B * ‖x‖)) := by
        gcongr
        · exact hH t ht
        · exact ((U.lift t).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hB t ⟨ht.1, ht.2.le⟩) (norm_nonneg x))
      _ = ‖z‖ * ε * B * ‖x‖ := by ring
  have hmean := norm_image_sub_le_of_norm_deriv_right_le_segment hfc hf hbound s hs
  have heq : f s - f 0 = star (V.evolution s)
      ((U.evolution s - V.evolution s) (domain.inclusion x)) := by
    dsimp [f]
    rw [U.initial, V.initial, star_one, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.one_apply, map_sub]
    congr 1
    exact (congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
      (Unitary.star_mul_self_of_mem (V.isUnitary s hs))).symm
  rw [heq, ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (V.isUnitary s hs))] at hmean
  convert hmean using 1
  rw [sub_zero]
  ring


end Adiabatic.Unbounded
