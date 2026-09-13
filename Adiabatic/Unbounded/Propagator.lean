import Adiabatic.Unbounded.Domain
import Adiabatic.Unbounded.StrongCalculus
import Adiabatic.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Domain-preserving strong propagators

This file specifies the evolution required for a common-domain unbounded
Hamiltonian and proves the inverse evolution equation from its forward
equation. Construction of such a propagator is a separate analytic theorem.
In particular, this structure is not itself an existence assertion.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A normalized unitary strong evolution preserving a common domain in both
directions. `K` is a bounded additional generator; physical evolution has `K=0`. -/
structure StrongPropagator (domain : CommonDomain D E)
    (H : ℝ → D →L[ℂ] E) (K : ℝ → E →L[ℂ] E) (z : ℂ) where
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
  strong_derivative : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt (fun a => evolution a (domain.inclusion x))
      (z • H t (lift t x) + K t (evolution t (domain.inclusion x))) (Icc 0 1) t

namespace StrongPropagator

variable {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E}
  {K : ℝ → E →L[ℂ] E} {z : ℂ} (U : StrongPropagator domain H K z)

/-- Unitary evolution is uniformly bounded, including the zero space. -/
theorem norm_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖U.evolution t‖ ≤ 1 := by
  apply (U.evolution t).opNorm_le_bound zero_le_one
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (U.isUnitary t ht) x, one_mul]

/-- The adjoint family has the same uniform bound. -/
theorem adjoint_norm_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖star (U.evolution t)‖ ≤ 1 := by
  apply (star (U.evolution t)).opNorm_le_bound zero_le_one
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (U.isUnitary t ht)) x,
    one_mul]

/-- The adjoint family is strongly continuous; no norm continuity is used. -/
theorem adjoint_strong_continuous (x : E) :
    ContinuousOn (fun t => star (U.evolution t) x) (Icc (0 : ℝ) 1) := by
  intro t ht
  apply continuousWithinAt_inverse_apply_of_strong (A := U.evolution) (M := 1)
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact U.adjoint_norm_le_one ha
  · filter_upwards [self_mem_nhdsWithin] with a ha
    intro y
    exact congrArg (fun B : E →L[ℂ] E => B y)
      (Unitary.star_mul_self_of_mem (U.isUnitary a ha))
  · exact congrArg (fun B : E →L[ℂ] E => B x)
      (Unitary.mul_star_self_of_mem (U.isUnitary t ht))
  · exact U.strong_continuous _ t ht

/-- The forward domain map cancels its inverse domain map. -/
theorem lift_inverseLift {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    U.lift t (U.inverseLift t x) = x := by
  apply domain.injective
  rw [← U.preserves_domain t ht, ← U.inverse_preserves_domain t ht]
  exact congrArg (fun B : E →L[ℂ] E => B (domain.inclusion x))
    (Unitary.mul_star_self_of_mem (U.isUnitary t ht))

/-- The strong adjoint equation follows from actual inverse differentiation
and domain preservation. -/
theorem adjoint_strong_derivative (x : D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun a => star (U.evolution a) (domain.inclusion x))
      (-(z • star (U.evolution t) (H t x)) -
        star (U.evolution t) (K t (domain.inclusion x))) (Icc 0 1) t := by
  have hV : HasDerivWithinAt
      (fun a => U.evolution a (star (U.evolution t) (domain.inclusion x)))
      (z • H t x + K t (domain.inclusion x)) (Icc 0 1) t := by
    rw [U.inverse_preserves_domain t ht]
    have h := U.strong_derivative (U.inverseLift t x) t ht
    rw [U.lift_inverseLift ht, U.preserves_domain t ht, U.lift_inverseLift ht] at h
    exact h
  have hinv := hasDerivWithinAt_inverse_apply_of_strong (A := U.evolution)
    (B := fun a => star (U.evolution a)) (M := 1)
    (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ‖star (U.evolution a)‖ ≤ 1 from by
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact U.adjoint_norm_le_one ha)
    (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ∀ y,
      star (U.evolution a) (U.evolution a y) = y from by
      filter_upwards [self_mem_nhdsWithin] with a ha
      intro y
      exact congrArg (fun B : E →L[ℂ] E => B y)
        (Unitary.star_mul_self_of_mem (U.isUnitary a ha)))
    (show U.evolution t (star (U.evolution t) (domain.inclusion x)) = domain.inclusion x from
      congrArg (fun B : E →L[ℂ] E => B (domain.inclusion x))
        (Unitary.mul_star_self_of_mem (U.isUnitary t ht)))
    (U.adjoint_strong_continuous _ t ht) hV
  simpa only [map_add, map_smul, neg_add_rev, sub_eq_add_neg, add_comm] using hinv

/-- Domain-preserving unitary solutions of the same strong equation agree
on the unit interval. The comparison is differentiated only on the dense domain. -/
theorem unique (V : StrongPropagator domain H K z) :
    EqOn U.evolution V.evolution (Icc (0 : ℝ) 1) := by
  have hzero (x : D) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt
        (fun a => star (V.evolution a) (U.evolution a (domain.inclusion x)))
        0 (Icc 0 1) t := by
    have hw := V.adjoint_strong_derivative (U.lift t x) ht
    rw [← U.preserves_domain t ht] at hw
    convert hasDerivWithinAt_apply_of_strong
      (A := fun a => star (V.evolution a))
      (v := fun a => U.evolution a (domain.inclusion x))
      (show ∀ᶠ a in 𝓝[Icc (0 : ℝ) 1] t, ‖star (V.evolution a)‖ ≤ 1 from by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact V.adjoint_norm_le_one ha)
      (V.adjoint_strong_continuous _ t ht) hw (U.strong_derivative x t ht) using 1
    simp only [map_add, map_smul]
    module
  intro t ht
  have hprod : star (V.evolution t) * U.evolution t = 1 := by
    apply ContinuousLinearMap.ext
    have hdense (x : D) :
        (star (V.evolution t) * U.evolution t) (domain.inclusion x) =
          (1 : E →L[ℂ] E) (domain.inclusion x) := by
      have hc := constant_of_derivWithin_zero
        (fun a ha => (hzero x a ha).differentiableWithinAt)
        (fun a ha => (hzero x a ⟨ha.1, ha.2.le⟩).derivWithin
          (uniqueDiffOn_Icc_zero_one a ⟨ha.1, ha.2.le⟩)) t ht
      simpa only [U.initial, V.initial, star_one, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply] using hc
    intro y
    exact congrFun (domain.dense.equalizer
      (star (V.evolution t) * U.evolution t).continuous
      (1 : E →L[ℂ] E).continuous (funext hdense)) y
  calc
    U.evolution t = (V.evolution t * star (V.evolution t)) * U.evolution t := by
      rw [Unitary.mul_star_self_of_mem (V.isUnitary t ht), one_mul]
    _ = V.evolution t * (star (V.evolution t) * U.evolution t) := mul_assoc _ _ _
    _ = V.evolution t := by rw [hprod, mul_one]

end StrongPropagator
end Adiabatic.Unbounded
