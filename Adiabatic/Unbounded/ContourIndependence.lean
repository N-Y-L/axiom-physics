import Adiabatic.Unbounded.ResolventSpectrum

/-!
# Independence of the enclosing spectral circle

Two resolvent circles select the same projection whenever they enclose the
same points of the actual unbounded spectrum. This permits local fixed
contours for a band described by continuous moving endpoints.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Complex Metric Set
open Adiabatic.Infinite
open scoped Classical

/-- The spectral cutoff after transforming to a bounded reference resolvent. -/
def rationalCutoff (p c : ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else diskIndicator c r (p + w⁻¹)

theorem normalized_integral_rationalKernel_eq {p c w : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, (z - p) * w - 1 ≠ 0) :
    contourNormalization * (∮ z in C(c, r), rationalResolventKernel p z w) =
      rationalCutoff p c r w := by
  by_cases hw : w = 0
  · subst w
    simp [rationalResolventKernel, rationalCutoff, circleIntegral]
  · have hn : p + w⁻¹ ∉ sphere c r := by
      intro hz
      exact hgap _ hz (by simp [inv_mul_cancel₀ hw])
    have he : (∮ z in C(c, r), rationalResolventKernel p z w) =
        (∮ z in C(c, r), (z - (p + w⁻¹))⁻¹) := by
      congr 1
      funext z
      exact rationalResolventKernel_eq hw
    rw [he, normalized_circle_integral_resolvent hr hn, rationalCutoff, if_neg hw]

section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

/-- The unbounded resolvent contour is an explicit spectral cutoff under bounded CFC. -/
theorem rationalRieszProjection_eq_cfc {a : A} (ha : IsStarNormal a)
    {p c : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    rationalRieszProjection a p c r = cfc (rationalCutoff p c r) a := by
  let Q : C(spectrum ℂ a, ℂ) :=
    contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)
  have hi : CircleIntegrable (rationalSpectralResolvent a p) c r :=
    (continuousOn_rationalSpectralResolvent ha hgap).circleIntegrable hr.le
  have hval (w : spectrum ℂ a) : Q w = rationalCutoff p c r w := by
    change contourNormalization * (ContinuousMap.evalCLM ℂ w)
      (∮ z in C(c, r), rationalSpectralResolvent a p z) = _
    rw [← circleIntegral_comp_comm _ hi]
    have he : (∮ z in C(c, r), (ContinuousMap.evalCLM ℂ w) (rationalSpectralResolvent a p z)) =
        (∮ z in C(c, r), rationalResolventKernel p z w) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      exact rationalSpectralResolvent_apply ha (hgap z hz) w
    rw [he]
    exact normalized_integral_rationalKernel_eq hr
      (fun z hz => rational_denominator_ne_zero ha (hgap z hz) w.property)
  have he : rationalRieszProjection a p c r = cfcL ha Q := by
    rw [rationalRieszProjection]
    have he' : (∮ z in C(c, r), cfc (rationalResolventKernel p z) a) =
        (∮ z in C(c, r), cfcL ha (rationalSpectralResolvent a p z)) := by
      apply circleIntegral.integral_congr hr.le
      intro z _
      exact cfc_eq_cfcL_mkD _ a ha
    rw [he', circleIntegral_comp_comm _ hi]
    exact ((cfcL ha).map_smul contourNormalization _).symm
  rw [he, cfc_eq_cfcL_mkD _ a ha]
  have hfun : (spectrum ℂ a).restrict (rationalCutoff p c r) = Q :=
    funext fun w => (hval w).symm
  rw [hfun, ContinuousMap.mkD_of_continuous Q.continuous]
  rfl

end FunctionalCalculus

namespace CommonDomain

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E)

/-- Contours enclosing the same actual spectrum define the same spectral projection. -/
theorem rieszProjection_eq_of_spectral_membership (hH : domain.IsSelfAdjoint H)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (gap₁ : ∀ z ∈ sphere c₁ r₁, z ∈ domain.resolventSet H)
    (gap₂ : ∀ z ∈ sphere c₂ r₂, z ∈ domain.resolventSet H)
    (hregion : ∀ w ∈ domain.spectrum H, w ∈ ball c₁ r₁ ↔ w ∈ ball c₂ r₂) :
    domain.rieszProjection H c₁ r₁ = domain.rieszProjection H c₂ r₂ := by
  have hp : Complex.I.im ≠ 0 := by simp
  have hp' := domain.mem_resolventSet_of_im_ne_zero H hH Complex.I hp
  have hn := domain.physicalInverseShift_isStarNormal H hH Complex.I hp
  rw [domain.rieszProjection_eq_rational H hH hp hr₁.le gap₁,
    domain.rieszProjection_eq_rational H hH hp hr₂.le gap₂,
    rationalRieszProjection_eq_cfc hn hr₁ (fun z hz => domain.rationalPencil_isUnit H hp' (gap₁ z hz)),
    rationalRieszProjection_eq_cfc hn hr₂ (fun z hz => domain.rationalPencil_isUnit H hp' (gap₂ z hz))]
  apply cfc_congr
  intro w hw
  by_cases hw0 : w = 0
  · simp [rationalCutoff, hw0]
  · have hs := domain.mem_spectrum_of_mem_resolvent_spectrum H hH Complex.I hp hw hw0
    simp only [rationalCutoff, if_neg hw0, diskIndicator]
    rw [hregion _ hs]

/-- Equality of spectral regions also identifies their common-domain projection lifts. -/
theorem rieszProjectionLift_eq_of_spectral_membership (hH : domain.IsSelfAdjoint H)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (gap₁ : ∀ z ∈ sphere c₁ r₁, z ∈ domain.resolventSet H)
    (gap₂ : ∀ z ∈ sphere c₂ r₂, z ∈ domain.resolventSet H)
    (hregion : ∀ w ∈ domain.spectrum H, w ∈ ball c₁ r₁ ↔ w ∈ ball c₂ r₂) :
    domain.rieszProjectionLift H c₁ r₁ hr₁.le = domain.rieszProjectionLift H c₂ r₂ hr₂.le := by
  ext x
  apply domain.injective
  change (domain.inclusion.comp (domain.rieszProjectionLift H c₁ r₁ hr₁.le)) x =
    (domain.inclusion.comp (domain.rieszProjectionLift H c₂ r₂ hr₂.le)) x
  rw [domain.inclusion_rieszProjectionLift H hH hr₁.le gap₁,
    domain.inclusion_rieszProjectionLift H hH hr₂.le gap₂,
    domain.rieszProjection_eq_of_spectral_membership H hH hr₁ hr₂ gap₁ gap₂ hregion]

end CommonDomain
end Adiabatic.Unbounded
