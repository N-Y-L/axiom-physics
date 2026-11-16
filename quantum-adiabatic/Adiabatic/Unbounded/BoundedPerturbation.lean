import Adiabatic.Unbounded.Domain
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Bounded self-adjoint perturbations on a common domain

Adding a bounded self-adjoint operator preserves unbounded
self-adjointness and the original domain. The proof identifies the adjoint
domain of the perturbed operator.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E)

/-- A bounded self-adjoint perturbation preserves the full common domain. -/
theorem isSelfAdjoint_add_bounded (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)
    (B : E →L[ℂ] E) (hB : star B = B) :
    domain.IsSelfAdjoint (H + B.comp domain.inclusion) := by
  let C := domain.operator (H + B.comp domain.inclusion)
  have hd : Dense (C.domain : Set E) := domain.dense
  have hBi (x y : E) : inner ℂ (B x) y = inner ℂ x (B y) := by
    exact (ContinuousLinearMap.eq_adjoint_iff B B).mp hB.symm x y
  have hs : C.IsFormalAdjoint C := by
    intro x y
    obtain ⟨u, rfl⟩ := domain.rangeEquiv.surjective x
    obtain ⟨v, rfl⟩ := domain.rangeEquiv.surjective y
    simp only [C, domain.operator_apply, rangeEquiv_coe]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      inner_add_left, inner_add_right, hBi, domain.inner_map H hH]
  have hle : C ≤ C.adjoint := hs.le_adjoint hd
  have hsub : C.adjoint.domain ≤ C.domain := by
    intro y hy
    let y' : C.adjoint.domain := ⟨y, hy⟩
    have hf : ∀ x : (domain.operator H).domain,
        inner ℂ (C.adjoint y' - B y) (x : E) = inner ℂ y (domain.operator H x) := by
      intro x
      obtain ⟨v, rfl⟩ := domain.rangeEquiv.surjective x
      have h := C.adjoint_isFormalAdjoint hd y' (domain.rangeEquiv v)
      simp only [C, domain.operator_apply, rangeEquiv_coe] at h
      change inner ℂ (C.adjoint y') (domain.inclusion v) =
        inner ℂ y ((H + B.comp domain.inclusion) v) at h
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right] at h
      simp only [domain.operator_apply, rangeEquiv_coe]
      change inner ℂ (C.adjoint y' - B y) (domain.inclusion v) = inner ℂ y (H v)
      rw [inner_sub_left, h, hBi]
      exact add_sub_cancel_right _ _
    have hyadj := (domain.operator H).mem_adjoint_domain_of_exists y
      ⟨C.adjoint y' - B y, hf⟩
    have hA : (domain.operator H).adjoint = domain.operator H := hH
    have hyA : y ∈ (domain.operator H).domain := by
      rw [← hA]
      exact hyadj
    exact hyA
  change C.adjoint = C
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hsub)).symm

/-- The skew correction in adiabatic evolution is a self-adjoint Hamiltonian perturbation. -/
theorem isSelfAdjoint_add_skew_correction (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)
    (K : E →L[ℂ] E) (hK : star K = -K) (z : ℂ) (hz : star z = -z) :
    domain.IsSelfAdjoint (H + (z⁻¹ • K).comp domain.inclusion) := by
  apply domain.isSelfAdjoint_add_bounded H hH
  simp [star_smul, star_inv₀, hz, hK]

end Adiabatic.Unbounded.CommonDomain
