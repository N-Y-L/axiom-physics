import Adiabatic.Unbounded.RieszCommutator
import Adiabatic.Unbounded.SmoothGluing

/-!
# A global C¹ domain commutator solution

Local spectral contours provide domain-valued commutator solutions. A finite
smooth partition of unity combines them on the compact time interval. The
commutator equation is linear in its solution, so the patch preserves it.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Metric

namespace CommonDomain

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E)

/-- The unbounded domain commutator as a real-linear map of its lifted solution. -/
def commutatorLinearMap (H : D →L[ℂ] E) : (E →L[ℂ] D) →ₗ[ℝ] D →L[ℂ] E where
  toFun L := (H.comp L).comp domain.inclusion - (domain.inclusion.comp L).comp H
  map_add' L M := by ext x; simp; abel
  map_smul' a L := by ext x; simp [smul_sub]

/-- Local resolvent circles construct a global C¹ solution of the
unbounded Kato commutator equation. -/
theorem exists_contDiffOn_commutatorLift_of_local_contours
    {H : ℝ → D →L[ℂ] E} {P : ℝ → E →L[ℂ] E} {s : Set ℝ}
    (hs : IsCompact s) (hdiff : UniqueDiffOn ℝ s)
    (hH : ContDiffOn ℝ 1 H s) (hP : ContDiffOn ℝ 2 P s)
    (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (H t))
    (hloc : ∀ t ∈ s, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        (∀ u ∈ s ∩ U, ∀ z ∈ sphere c r, z ∈ domain.resolventSet (H u)) ∧
        ∀ u ∈ s ∩ U, P u = domain.rieszProjection (H u) c r) :
    ∃ L : ℝ → E →L[ℂ] D, ContDiffOn ℝ 1 L s ∧ ∀ t ∈ s, ∀ x : D,
      H t (L t (domain.inclusion x)) - domain.inclusion (L t (H t x)) =
        katoGenerator (P t) (derivWithin P s t) (domain.inclusion x) := by
  let B : ℝ → E →L[ℂ] E := derivWithin P s
  let K : ℝ → E →L[ℂ] E := fun t => katoGenerator (P t) (B t)
  have hb : ContDiffOn ℝ 1 B s := hP.derivWithin hdiff (by norm_num)
  have hl : ∀ t ∈ s, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ∃ g : ℝ → E →L[ℂ] D, ContDiffOn ℝ 1 g (s ∩ U) ∧
        ∀ u ∈ s ∩ U, domain.commutatorLinearMap (H u) (g u) = (K u).comp domain.inclusion := by
    intro t ht
    obtain ⟨U, ho, htu, c, r, hr, hgap, hpeq⟩ := hloc t ht
    refine ⟨U, ho, htu, fun u => domain.contourCommutatorLift (H u) (B u) c r hr.le,
      domain.contDiffOn_contourCommutatorLift (hH.mono inter_subset_left)
        (hb.mono inter_subset_left) (fun u hu => hsa u hu.1) hr.le hgap, ?_⟩
    intro u hu
    ext x
    have he := domain.contourCommutator_commutator (H u) (hsa u hu.1) (B u) hr.le (hgap u hu) x
    rw [← hpeq u hu] at he
    exact he
  obtain ⟨L, hL, hcomm⟩ := exists_contDiffOn_linear_solution hs
    (fun t => domain.commutatorLinearMap (H t)) (fun t => (K t).comp domain.inclusion) hl
  refine ⟨L, hL, ?_⟩
  intro t ht x
  exact DFunLike.congr_fun (hcomm t ht) x

end CommonDomain
end Adiabatic.Unbounded
