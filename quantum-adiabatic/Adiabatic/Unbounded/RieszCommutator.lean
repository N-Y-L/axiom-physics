import Adiabatic.Unbounded.RieszProjection

/-!
# Domain-valued contour commutator solution

The contour sandwich provides a bounded map into the common domain. Its
inclusion in the physical Hilbert space solves the unbounded commutator
equation on that domain and varies smoothly in operator norm.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Metric
open Adiabatic.Infinite

section RationalSandwich

variable {A : Type*} [CStarAlgebra A]

/-- The bounded rational factors in a two-resolvent contour sandwich. -/
def rationalSandwich (a b : A) (p c : ℂ) (r : ℝ) : C(sphere c r, A) :=
  Ring.inverse (rationalContourPencil a p c r) * ContinuousMap.const _ b *
    ContinuousMap.const _ a * Ring.inverse (rationalContourPencil a p c r)

theorem contDiffOn_rationalSandwich {a b : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) {p c : ℂ} {r : ℝ}
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, IsUnit ((z - p) • a t - 1)) :
    ContDiffOn ℝ n (fun t => rationalSandwich (a t) (b t) p c r) s := by
  have hi := contDiffOn_rationalContourInverse ha hgap
  have hca := (ContinuousLinearMap.const ℝ (M := A) (sphere c r)).contDiff.comp_contDiffOn ha
  have hcb := (ContinuousLinearMap.const ℝ (M := A) (sphere c r)).contDiff.comp_contDiffOn hb
  exact ((hi.mul hcb).mul hca).mul hi

end RationalSandwich

namespace CommonDomain

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E)

/-- The commutator solution lifted boundedly into the common operator domain. -/
def contourCommutatorLift (B : E →L[ℂ] E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : E →L[ℂ] D :=
  (-contourNormalization) • (domain.inverseShift H Complex.I).comp
    (circleIntegralCLM c r hr (rationalSandwich
      (domain.physicalInverseShift H Complex.I) B Complex.I c r))

/-- The physical bounded operator associated to the domain-valued contour solution. -/
def contourCommutator (B : E →L[ℂ] E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : E →L[ℂ] E :=
  domain.inclusion.comp (domain.contourCommutatorLift H B c r hr)

theorem contDiffOn_contourCommutatorLift {K : ℝ → D →L[ℂ] E}
    {B : ℝ → E →L[ℂ] E} {s : Set ℝ} {n : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K s) (hB : ContDiffOn ℝ n B s)
    (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t)) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∈ domain.resolventSet (K t)) :
    ContDiffOn ℝ n (fun t => domain.contourCommutatorLift (K t) (B t) c r hr) s := by
  have hb := domain.contDiffOn_physicalReferenceResolvent hK hsa
  have hs := contDiffOn_rationalSandwich hb hB (fun t ht z hz => domain.rationalPencil_isUnit (K t)
    (domain.mem_resolventSet_of_im_ne_zero (K t) (hsa t ht) Complex.I (by simp)) (hgap t ht z hz))
  have hi := (((circleIntegralCLM (E := E →L[ℂ] E) c r hr).restrictScalars ℝ).contDiff).comp_contDiffOn hs
  exact ContDiffOn.const_smul (-contourNormalization)
    (((isBoundedBilinearMap_comp (𝕜 := ℂ) (E := E) (F := E) (G := D)).contDiff.restrict_scalars ℝ).comp₂_contDiffOn
      (domain.contDiffOn_referenceResolvent hK hsa) hi)

theorem contDiffOn_contourCommutator {K : ℝ → D →L[ℂ] E}
    {B : ℝ → E →L[ℂ] E} {s : Set ℝ} {n : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K s) (hB : ContDiffOn ℝ n B s)
    (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t)) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∈ domain.resolventSet (K t)) :
    ContDiffOn ℝ n (fun t => domain.contourCommutator (K t) (B t) c r hr) s := by
  exact (((ContinuousLinearMap.compL ℂ E D E domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn
    (domain.contDiffOn_contourCommutatorLift hK hB hsa hr hgap)

theorem contourCommutatorLift_eq_integral (hH : domain.IsSelfAdjoint H)
    (B : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) :
    domain.contourCommutatorLift H B c r hr = (-contourNormalization) •
      (∮ z in C(c, r), (domain.inverseShift H z).comp (B * domain.physicalInverseShift H z)) := by
  let b := domain.physicalInverseShift H Complex.I
  let F := rationalSandwich b B Complex.I c r
  let L : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] D :=
    ContinuousLinearMap.compL ℂ E E D (domain.inverseShift H Complex.I)
  have hp : Complex.I ∈ domain.resolventSet H :=
    domain.mem_resolventSet_of_im_ne_zero H hH Complex.I (by simp)
  have hu (z : ℂ) (hz : z ∈ sphere c r) : IsUnit ((z - Complex.I) • b - 1) :=
    domain.rationalPencil_isUnit H hp (hgap z hz)
  have hi : CircleIntegrable (circleExtension F) c r :=
    (continuousOn_circleExtension F).circleIntegrable hr
  change (-contourNormalization) • L (circleIntegralCLM c r hr F) = _
  rw [circleIntegralCLM_apply, ← circleIntegral_comp_comm L hi]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [show circleExtension F z = F ⟨z, hz⟩ from circleExtension_apply F ⟨z, hz⟩]
  change (domain.inverseShift H Complex.I).comp
    (rationalSandwich b B Complex.I c r ⟨z, hz⟩) = _
  simp only [rationalSandwich, ContinuousMap.mul_apply, ContinuousMap.const_apply,
    rationalContourInverse_apply hu]
  have hd := domain.rationalDomainResolvent_eq H hp (hgap z hz)
  have he := domain.rationalResolvent_eq H hp (hgap z hz)
  ext x
  have hd' (y : E) := DFunLike.congr_fun hd y
  have he' (y : E) := DFunLike.congr_fun he y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply] at hd'
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] at he'
  change (domain.inverseShift H Complex.I)
    (Ring.inverse ((z - Complex.I) • b - 1)
      (B (b (Ring.inverse ((z - Complex.I) • b - 1) x)))) = _
  rw [hd', he']
  simp

/-- The constructed spectral projection commutes with the unbounded operator on its domain. -/
theorem rieszProjection_commutes (hH : domain.IsSelfAdjoint H)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) (x : D) :
    H (domain.rieszProjectionLift H c r hr (domain.inclusion x)) =
      domain.rieszProjection H c r (H x) := by
  let T : (E →L[ℂ] D) →L[ℂ] E :=
    H.comp (ContinuousLinearMap.apply ℂ D (domain.inclusion x)) -
      domain.inclusion.comp (ContinuousLinearMap.apply ℂ D (H x))
  have hi : CircleIntegrable (domain.inverseShift H) c r :=
    (domain.continuousOn_inverseShift H hgap).circleIntegrable hr
  have ht : T (domain.rieszProjectionLift H c r hr) = 0 := by
    rw [domain.rieszProjectionLift_eq_integral H hH hr hgap, T.map_smul,
      ← circleIntegral_comp_comm T hi]
    have he : (∮ z in C(c, r), T (domain.inverseShift H z)) = 0 := by
      calc
        _ = (∮ z in C(c, r), (0 : E)) := by
          apply circleIntegral.integral_congr hr
          intro z hz
          change H (domain.inverseShift H z (domain.inclusion x)) -
            domain.inclusion (domain.inverseShift H z (H x)) = 0
          exact sub_eq_zero.mpr (domain.map_inverseShift_inclusion H z (hgap z hz) x)
        _ = 0 := by simp [circleIntegral]
    rw [he, smul_zero]
  change H (domain.rieszProjectionLift H c r hr (domain.inclusion x)) -
    (domain.inclusion.comp (domain.rieszProjectionLift H c r hr)) (H x) = 0 at ht
  rw [domain.inclusion_rieszProjectionLift H hH hr hgap] at ht
  exact sub_eq_zero.mp ht

/-- The contour construction solves the unbounded commutator equation on D. -/
theorem contourCommutator_commutator (hH : domain.IsSelfAdjoint H)
    (B : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) (x : D) :
    H (domain.contourCommutatorLift H B c r hr (domain.inclusion x)) -
      domain.contourCommutator H B c r hr (H x) =
        B (domain.rieszProjection H c r (domain.inclusion x)) -
          domain.rieszProjection H c r (B (domain.inclusion x)) := by
  let T : (E →L[ℂ] D) →L[ℂ] E :=
    H.comp (ContinuousLinearMap.apply ℂ D (domain.inclusion x)) -
      domain.inclusion.comp (ContinuousLinearMap.apply ℂ D (H x))
  let S : (E →L[ℂ] E) →L[ℂ] E :=
    B.comp (ContinuousLinearMap.apply ℂ E (domain.inclusion x)) -
      ContinuousLinearMap.apply ℂ E (B (domain.inclusion x))
  have hrcont := domain.continuousOn_inverseShift H hgap
  have hpcont : ContinuousOn (domain.physicalInverseShift H) (sphere c r) :=
    continuousOn_const.clm_comp hrcont
  have hiR : CircleIntegrable (domain.physicalInverseShift H) c r := hpcont.circleIntegrable hr
  have hiF : CircleIntegrable
      (fun z => (domain.inverseShift H z).comp (B * domain.physicalInverseShift H z)) c r :=
    (hrcont.clm_comp (continuousOn_const.mul hpcont)).circleIntegrable hr
  change T (domain.contourCommutatorLift H B c r hr) = S (domain.rieszProjection H c r)
  rw [domain.contourCommutatorLift_eq_integral H hH B hr hgap, rieszProjection,
    T.map_smul, S.map_smul, ← circleIntegral_comp_comm T hiF, ← circleIntegral_comp_comm S hiR]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  exact domain.inverseShift_sandwich_commutator H B z (hgap z hz) x

end CommonDomain
end Adiabatic.Unbounded
