import Adiabatic.Infinite.RieszCommutator
import Adiabatic.Unbounded.Resolvent

/-!
# Spectral contours through a bounded resolvent

An unbounded Hamiltonian is represented by its bounded normal resolvent at a
nonreal reference point. Rational functional calculus then reconstructs the
original resolvent contour and its spectral projection.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Complex Metric Set Topology
open Adiabatic.Infinite
open scoped Classical

/-- The scalar resolvent after changing variables to a fixed bounded resolvent. -/
def rationalResolventKernel (p z w : ℂ) : ℂ := w / ((z - p) * w - 1)

theorem rationalResolventKernel_eq {p z w : ℂ} (hw : w ≠ 0) :
    rationalResolventKernel p z w = (z - (p + w⁻¹))⁻¹ := by
  have he : (z - p) * w - 1 = (z - (p + w⁻¹)) * w := by
    field_simp
    ring
  rw [rationalResolventKernel, he, div_eq_mul_inv, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ hw, one_mul]

theorem normalized_integral_rationalKernel {p c w : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, (z - p) * w - 1 ≠ 0) :
    contourNormalization * (∮ z in C(c, r), rationalResolventKernel p z w) = 0 ∨
      contourNormalization * (∮ z in C(c, r), rationalResolventKernel p z w) = 1 := by
  by_cases hw : w = 0
  · subst w
    left
    simp [rationalResolventKernel, circleIntegral]
  · have hn : p + w⁻¹ ∉ sphere c r := by
      intro hz
      exact hgap _ hz (by simp [inv_mul_cancel₀ hw])
    have he : (∮ z in C(c, r), rationalResolventKernel p z w) =
        (∮ z in C(c, r), (z - (p + w⁻¹))⁻¹) := by
      congr 1
      funext z
      exact rationalResolventKernel_eq hw
    rw [he, normalized_circle_integral_resolvent hr hn]
    unfold diskIndicator
    split_ifs <;> simp

section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

/-- The rational resolvent as a continuous function on a bounded operator's spectrum. -/
def rationalSpectralResolvent (a : A) (p z : ℂ) : C(spectrum ℂ a, ℂ) :=
  ContinuousMap.mkD ((spectrum ℂ a).restrict (rationalResolventKernel p z)) 0

theorem cfc_rational_denominator {a : A} (ha : IsStarNormal a) (p z : ℂ) :
    cfc (fun w : ℂ => (z - p) * w - 1) a = (z - p) • a - 1 := by
  rw [cfc_sub (fun w : ℂ => (z - p) * w) (fun _ : ℂ => 1),
    cfc_const_one ℂ a ha, cfc_mul (fun _ : ℂ => z - p) (fun w : ℂ => w) a,
    cfc_const (z - p) a ha, cfc_id' ℂ a ha, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

theorem rational_denominator_ne_zero {a : A} (ha : IsStarNormal a) {p z : ℂ}
    (hunit : IsUnit ((z - p) • a - 1)) {w : ℂ} (hw : w ∈ spectrum ℂ a) :
    (z - p) * w - 1 ≠ 0 := by
  have hi : IsUnit (cfc (fun w : ℂ => (z - p) * w - 1) a) :=
    (cfc_rational_denominator ha p z).symm ▸ hunit
  exact (isUnit_cfc_iff _ a (ha := ha)).mp hi w hw

theorem cfc_rationalResolventKernel {a : A} (ha : IsStarNormal a) {p z : ℂ}
    (hunit : IsUnit ((z - p) • a - 1)) :
    cfc (rationalResolventKernel p z) a = a * Ring.inverse ((z - p) • a - 1) := by
  change cfc (fun w : ℂ => w / ((z - p) * w - 1)) a = _
  simp_rw [div_eq_mul_inv]
  rw [cfc_mul (fun w : ℂ => w) (fun w => ((z - p) * w - 1)⁻¹) a
    (hf := continuousOn_id)
    (hg := (by fun_prop : ContinuousOn (fun w : ℂ => (z - p) * w - 1)
      (spectrum ℂ a)).inv₀ (fun w hw => rational_denominator_ne_zero ha hunit hw)),
    cfc_id' ℂ a ha,
    cfc_inv (fun w : ℂ => (z - p) * w - 1) a
      (fun w hw => rational_denominator_ne_zero ha hunit hw),
    cfc_rational_denominator ha p z]

theorem rationalSpectralResolvent_apply {a : A} (ha : IsStarNormal a) {p z : ℂ}
    (hunit : IsUnit ((z - p) • a - 1)) (w : spectrum ℂ a) :
    rationalSpectralResolvent a p z w = rationalResolventKernel p z w := by
  apply ContinuousMap.mkD_apply_of_continuousOn
  exact continuousOn_id.div (by fun_prop)
    (fun x hx => rational_denominator_ne_zero ha hunit hx)

theorem continuousOn_rationalSpectralResolvent {a : A} (ha : IsStarNormal a)
    {p c : ℂ} {r : ℝ} (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    ContinuousOn (rationalSpectralResolvent a p) (sphere c r) := by
  apply ContinuousMap.continuousOn_mkD_restrict_of_uncurry
  apply continuousOn_snd.div (by fun_prop)
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  exact rational_denominator_ne_zero ha (hgap z hz) hw

/-- The bounded rational contour projection. -/
def rationalRieszProjection (a : A) (p c : ℂ) (r : ℝ) : A :=
  contourNormalization • (∮ z in C(c, r), cfc (rationalResolventKernel p z) a)

/-- The integrated scalar rational resolvent is an idempotent real-valued function. -/
theorem normalized_rationalSpectralIntegral_projection {a : A} (ha : IsStarNormal a)
    {p c : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    let f := contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)
    f * f = f ∧ star f = f := by
  have hi : CircleIntegrable (rationalSpectralResolvent a p) c r :=
    (continuousOn_rationalSpectralResolvent ha hgap).circleIntegrable hr.le
  have hval (w : spectrum ℂ a) :
      (contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)) w = 0 ∨
      (contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)) w = 1 := by
    change contourNormalization * (ContinuousMap.evalCLM ℂ w)
      (∮ z in C(c, r), rationalSpectralResolvent a p z) = 0 ∨
      contourNormalization * (ContinuousMap.evalCLM ℂ w)
      (∮ z in C(c, r), rationalSpectralResolvent a p z) = 1
    rw [← circleIntegral_comp_comm _ hi]
    have he : (∮ z in C(c, r), (ContinuousMap.evalCLM ℂ w) (rationalSpectralResolvent a p z)) =
        (∮ z in C(c, r), rationalResolventKernel p z w) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      exact rationalSpectralResolvent_apply ha (hgap z hz) w
    rw [he]
    exact normalized_integral_rationalKernel hr
      (fun z hz => rational_denominator_ne_zero ha (hgap z hz) w.property)
  constructor
  · ext w
    simp only [ContinuousMap.mul_apply]
    rcases hval w with hw | hw <;> rw [hw] <;> simp
  · ext w
    change star ((contourNormalization •
      (∮ z in C(c, r), rationalSpectralResolvent a p z)) w) =
      (contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)) w
    rcases hval w with hw | hw <;> rw [hw] <;> simp

/-- Rational resolvent contours yield orthogonal projections, including when zero
is in the spectrum of the bounded reference resolvent. -/
theorem rationalRieszProjection_isStarProjection {a : A} (ha : IsStarNormal a)
    {p c : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    rationalRieszProjection a p c r * rationalRieszProjection a p c r =
      rationalRieszProjection a p c r ∧
      star (rationalRieszProjection a p c r) = rationalRieszProjection a p c r := by
  have hi : CircleIntegrable (rationalSpectralResolvent a p) c r :=
    (continuousOn_rationalSpectralResolvent ha hgap).circleIntegrable hr.le
  have he : rationalRieszProjection a p c r = cfcL ha
      (contourNormalization • (∮ z in C(c, r), rationalSpectralResolvent a p z)) := by
    rw [rationalRieszProjection]
    have he' : (∮ z in C(c, r), cfc (rationalResolventKernel p z) a) =
        (∮ z in C(c, r), cfcL ha (rationalSpectralResolvent a p z)) := by
      apply circleIntegral.integral_congr hr.le
      intro z _
      exact cfc_eq_cfcL_mkD _ a ha
    rw [he', circleIntegral_comp_comm _ hi, map_smul]
  rw [he]
  change cfcHom ha _ * cfcHom ha _ = cfcHom ha _ ∧ star (cfcHom ha _) = cfcHom ha _
  obtain ⟨hmul, hstar⟩ := normalized_rationalSpectralIntegral_projection ha hr hgap
  constructor
  · rw [← map_mul, hmul]
  · rw [← map_star, hstar]

/-- The rational denominator assembled in the Banach algebra of contour functions. -/
def rationalContourPencil (a : A) (p c : ℂ) (r : ℝ) : C(sphere c r, A) :=
  (⟨fun z => ((z : ℂ) - p) • (1 : A), by fun_prop⟩ : C(sphere c r, A)) *
    ContinuousMap.const _ a - 1

@[simp] theorem rationalContourPencil_apply (a : A) (p c : ℂ) (r : ℝ) (z : sphere c r) :
    rationalContourPencil a p c r z = ((z : ℂ) - p) • a - 1 := by
  simp [rationalContourPencil]

theorem rationalContourPencil_isUnit {a : A} {p c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    IsUnit (rationalContourPencil a p c r) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro z
  simpa only [rationalContourPencil_apply] using hgap z z.property

theorem rationalContourInverse_apply {a : A} {p c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) (z : sphere c r) :
    Ring.inverse (rationalContourPencil a p c r) z = Ring.inverse (((z : ℂ) - p) • a - 1) := by
  apply (hgap z z.property).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (hgap z z.property)]
  have he := ContinuousMap.congr_fun
    (Ring.mul_inverse_cancel _ (rationalContourPencil_isUnit hgap)) z
  simpa only [ContinuousMap.mul_apply, rationalContourPencil_apply, ContinuousMap.one_apply] using he

/-- The normalized integral remaining after factoring out the bounded reference resolvent. -/
def rationalContourIntegral (a : A) (p c : ℂ) (r : ℝ) (hr : 0 ≤ r) : A :=
  contourNormalization • circleIntegralCLM c r hr (Ring.inverse (rationalContourPencil a p c r))

theorem rationalRieszProjection_eq_mul {a : A} (ha : IsStarNormal a)
    {p c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, IsUnit ((z - p) • a - 1)) :
    rationalRieszProjection a p c r = a * rationalContourIntegral a p c r hr := by
  rw [rationalRieszProjection, rationalContourIntegral, mul_smul_comm,
    ← circleIntegralCLM_mul_left, circleIntegralCLM_apply]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [show circleExtension (ContinuousMap.const (sphere c r) a *
      Ring.inverse (rationalContourPencil a p c r)) z =
      (ContinuousMap.const (sphere c r) a *
        Ring.inverse (rationalContourPencil a p c r)) ⟨z, hz⟩ from circleExtension_apply _ ⟨z, hz⟩]
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, rationalContourInverse_apply hgap]
  exact cfc_rationalResolventKernel ha (hgap z hz)

theorem contDiff_rationalContourPencil (p c : ℂ) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun a : A => rationalContourPencil a p c r) := by
  exact (contDiff_const.mul
    (ContinuousLinearMap.const ℝ (M := A) (sphere c r)).contDiff).sub contDiff_const

theorem contDiffOn_rationalContourInverse {a : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (ha : ContDiffOn ℝ n a s) {p c : ℂ} {r : ℝ}
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, IsUnit ((z - p) • a t - 1)) :
    ContDiffOn ℝ n (fun t => Ring.inverse (rationalContourPencil (a t) p c r)) s := by
  have hL := (contDiff_rationalContourPencil p c r).comp_contDiffOn ha
  intro t ht
  obtain ⟨u, hu⟩ := rationalContourPencil_isUnit (hgap t ht)
  have hi := contDiffAt_ringInverse (n := n) ℝ u
  rw [hu] at hi
  exact hi.comp_contDiffWithinAt t (hL t ht)

theorem contDiffOn_rationalContourIntegral {a : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (ha : ContDiffOn ℝ n a s) {p c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, IsUnit ((z - p) • a t - 1)) :
    ContDiffOn ℝ n (fun t => rationalContourIntegral (a t) p c r hr) s := by
  exact ContDiffOn.const_smul contourNormalization
    (((circleIntegralCLM (E := A) c r hr).restrictScalars ℝ).contDiff.comp_contDiffOn
      (contDiffOn_rationalContourInverse ha hgap))

end FunctionalCalculus

namespace CommonDomain

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E)

/-- Factor the resolvent pencil through a bounded reference resolvent. -/
theorem rationalPencil_eq {p : ℂ} (hp : p ∈ domain.resolventSet H) (z : ℂ) :
    (z - p) • domain.physicalInverseShift H p - 1 =
      -((domain.shift H z).comp (domain.inverseShift H p)) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    shift_apply, domain.map_inverseShift H p hp, physicalInverseShift_apply]
  module

/-- The original resolvent set makes the bounded rational denominator invertible. -/
theorem rationalPencil_isUnit {p z : ℂ} (hp : p ∈ domain.resolventSet H)
    (hz : z ∈ domain.resolventSet H) :
    IsUnit ((z - p) • domain.physicalInverseShift H p - 1) := by
  rw [domain.rationalPencil_eq H hp z]
  refine ⟨⟨-((domain.shift H z).comp (domain.inverseShift H p)),
    -((domain.shift H p).comp (domain.inverseShift H z)), ?_, ?_⟩, rfl⟩
  · ext x
    simp only [neg_mul_neg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      domain.inverseShift_shift H p hp, domain.shift_inverseShift H z hz,
      ContinuousLinearMap.one_apply]
  · ext x
    simp only [neg_mul_neg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      domain.inverseShift_shift H z hz, domain.shift_inverseShift H p hp,
      ContinuousLinearMap.one_apply]

theorem rationalPencil_inverse {p z : ℂ} (hp : p ∈ domain.resolventSet H)
    (hz : z ∈ domain.resolventSet H) :
    Ring.inverse ((z - p) • domain.physicalInverseShift H p - 1) =
      -((domain.shift H p).comp (domain.inverseShift H z)) := by
  apply (domain.rationalPencil_isUnit H hp hz).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (domain.rationalPencil_isUnit H hp hz),
    domain.rationalPencil_eq H hp z]
  ext x
  simp only [neg_mul_neg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
    domain.inverseShift_shift H p hp, domain.shift_inverseShift H z hz,
    ContinuousLinearMap.one_apply]

/-- Rational functional calculus recovers the physical resolvent at every regular point. -/
theorem rationalResolvent_eq {p z : ℂ} (hp : p ∈ domain.resolventSet H)
    (hz : z ∈ domain.resolventSet H) :
    domain.physicalInverseShift H p *
        Ring.inverse ((z - p) • domain.physicalInverseShift H p - 1) =
      -domain.physicalInverseShift H z := by
  rw [domain.rationalPencil_inverse H hp hz]
  ext x
  simp only [mul_neg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.comp_apply, physicalInverseShift_apply, domain.inverseShift_shift H p hp]

/-- The rational resolvent formula also holds with values in the full domain. -/
theorem rationalDomainResolvent_eq {p z : ℂ} (hp : p ∈ domain.resolventSet H)
    (hz : z ∈ domain.resolventSet H) :
    (domain.inverseShift H p).comp
        (Ring.inverse ((z - p) • domain.physicalInverseShift H p - 1)) =
      -domain.inverseShift H z := by
  rw [domain.rationalPencil_inverse H hp hz]
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg,
    domain.inverseShift_shift H p hp]

/-- Nonreal physical resolvents of an unbounded self-adjoint operator are normal. -/
theorem physicalInverseShift_isStarNormal (hH : domain.IsSelfAdjoint H)
    (p : ℂ) (hp : p.im ≠ 0) : IsStarNormal (domain.physicalInverseShift H p) := by
  rw [domain.physicalInverseShift_eq_physicalResolvent H hH p hp]
  constructor
  rw [domain.physicalResolvent_star H hH p hp]
  exact domain.physicalResolvent_commute H hH (starRingEnd ℂ p) p (by simpa using hp) hp

/-- The original resolvent contour defines a bounded spectral projection. -/
def rieszProjection (c : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (-contourNormalization) • (∮ z in C(c, r), domain.physicalInverseShift H z)

theorem rieszProjection_eq_rational (hH : domain.IsSelfAdjoint H)
    {p c : ℂ} {r : ℝ} (hp : p.im ≠ 0) (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) :
    domain.rieszProjection H c r = rationalRieszProjection (domain.physicalInverseShift H p) p c r := by
  have hp' := domain.mem_resolventSet_of_im_ne_zero H hH p hp
  have hn := domain.physicalInverseShift_isStarNormal H hH p hp
  rw [rieszProjection, rationalRieszProjection]
  have he : (∮ z in C(c, r), cfc (rationalResolventKernel p z) (domain.physicalInverseShift H p)) =
      (∮ z in C(c, r), (-1 : ℂ) • domain.physicalInverseShift H z) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    dsimp only
    rw [cfc_rationalResolventKernel hn (domain.rationalPencil_isUnit H hp' (hgap z hz)),
      domain.rationalResolvent_eq H hp' (hgap z hz)]
    simp
  rw [he, circleIntegral.integral_smul, smul_smul]
  congr 1
  ring

/-- A genuine common-domain spectral gap gives an actual orthogonal projection. -/
theorem rieszProjection_isStarProjection (hH : domain.IsSelfAdjoint H)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) :
    domain.rieszProjection H c r * domain.rieszProjection H c r = domain.rieszProjection H c r ∧
      star (domain.rieszProjection H c r) = domain.rieszProjection H c r := by
  have hp : Complex.I.im ≠ 0 := by simp
  rw [domain.rieszProjection_eq_rational H hH hp hr.le hgap]
  exact rationalRieszProjection_isStarProjection
    (domain.physicalInverseShift_isStarNormal H hH Complex.I hp) hr
    (fun z hz => domain.rationalPencil_isUnit H
      (domain.mem_resolventSet_of_im_ne_zero H hH Complex.I hp) (hgap z hz))

/-- The spectral projection has a bounded lift into the common operator domain. -/
def rieszProjectionLift (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : E →L[ℂ] D :=
  (domain.inverseShift H Complex.I).comp
    (rationalContourIntegral (domain.physicalInverseShift H Complex.I) Complex.I c r hr)

theorem inclusion_rieszProjectionLift (hH : domain.IsSelfAdjoint H)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) :
    domain.inclusion.comp (domain.rieszProjectionLift H c r hr) = domain.rieszProjection H c r := by
  have hp : Complex.I.im ≠ 0 := by simp
  rw [domain.rieszProjection_eq_rational H hH hp hr hgap,
    rationalRieszProjection_eq_mul (domain.physicalInverseShift_isStarNormal H hH Complex.I hp)
      hr (fun z hz => domain.rationalPencil_isUnit H
        (domain.mem_resolventSet_of_im_ne_zero H hH Complex.I hp) (hgap z hz))]
  rfl

theorem continuousOn_inverseShift {s : Set ℂ} (hs : s ⊆ domain.resolventSet H) :
    ContinuousOn (domain.inverseShift H) s := by
  intro z hz
  exact (domain.inverseShift_contDiffAt_parameter H z (hs hz) 0).continuousAt.continuousWithinAt

/-- The domain lift is the original contour integral in the domain norm. -/
theorem rieszProjectionLift_eq_integral (hH : domain.IsSelfAdjoint H)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∈ domain.resolventSet H) :
    domain.rieszProjectionLift H c r hr =
      (-contourNormalization) • (∮ z in C(c, r), domain.inverseShift H z) := by
  let b := domain.physicalInverseShift H Complex.I
  let F := Ring.inverse (rationalContourPencil b Complex.I c r)
  let L : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] D :=
    ContinuousLinearMap.compL ℂ E E D (domain.inverseShift H Complex.I)
  have hp : Complex.I ∈ domain.resolventSet H :=
    domain.mem_resolventSet_of_im_ne_zero H hH Complex.I (by simp)
  have hu (z : ℂ) (hz : z ∈ sphere c r) : IsUnit ((z - Complex.I) • b - 1) :=
    domain.rationalPencil_isUnit H hp (hgap z hz)
  have hi : CircleIntegrable (circleExtension F) c r :=
    (continuousOn_circleExtension F).circleIntegrable hr
  change L (contourNormalization • circleIntegralCLM c r hr F) = _
  rw [L.map_smul, circleIntegralCLM_apply, ← circleIntegral_comp_comm L hi]
  have he : (∮ z in C(c, r), L (circleExtension F z)) =
      (∮ z in C(c, r), (-1 : ℂ) • domain.inverseShift H z) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    dsimp only
    rw [show circleExtension F z = F ⟨z, hz⟩ from circleExtension_apply F ⟨z, hz⟩]
    change (domain.inverseShift H Complex.I).comp
      (Ring.inverse (rationalContourPencil b Complex.I c r) ⟨z, hz⟩) = _
    rw [rationalContourInverse_apply hu, domain.rationalDomainResolvent_eq H hp (hgap z hz)]
    simp
  rw [he, circleIntegral.integral_smul, smul_smul]
  congr 1
  ring

theorem contDiffOn_referenceResolvent {K : ℝ → D →L[ℂ] E} {s : Set ℝ} {n : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K s) (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t)) :
    ContDiffOn ℝ n (fun t => domain.inverseShift (K t) Complex.I) s := by
  intro t ht
  have hi := (domain.inverseShift_contDiffAt_operator (K t) Complex.I
    (domain.mem_resolventSet_of_im_ne_zero (K t) (hsa t ht) Complex.I (by simp)) n).restrict_scalars ℝ
  exact hi.comp_contDiffWithinAt t (hK t ht)

theorem contDiffOn_physicalReferenceResolvent {K : ℝ → D →L[ℂ] E} {s : Set ℝ}
    {n : WithTop ℕ∞} (hK : ContDiffOn ℝ n K s)
    (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t)) :
    ContDiffOn ℝ n (fun t => domain.physicalInverseShift (K t) Complex.I) s := by
  exact (((ContinuousLinearMap.compL ℂ E D E domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn
    (domain.contDiffOn_referenceResolvent hK hsa)

/-- The projection lift is as smooth in the domain norm as the Hamiltonian path. -/
theorem contDiffOn_rieszProjectionLift {K : ℝ → D →L[ℂ] E} {s : Set ℝ} {n : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K s) (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t))
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∈ domain.resolventSet (K t)) :
    ContDiffOn ℝ n (fun t => domain.rieszProjectionLift (K t) c r hr) s := by
  have hb := domain.contDiffOn_physicalReferenceResolvent hK hsa
  have hy := contDiffOn_rationalContourIntegral hb hr (fun t ht z hz =>
    domain.rationalPencil_isUnit (K t)
      (domain.mem_resolventSet_of_im_ne_zero (K t) (hsa t ht) Complex.I (by simp)) (hgap t ht z hz))
  exact ((isBoundedBilinearMap_comp (𝕜 := ℂ) (E := E) (F := E) (G := D)).contDiff.restrict_scalars ℝ).comp₂_contDiffOn
      (domain.contDiffOn_referenceResolvent hK hsa) hy

/-- An unbounded smooth Hamiltonian with a fixed spectral contour determines a
smooth bounded orthogonal projection, without a supplied projection path. -/
theorem contDiffOn_rieszProjection {K : ℝ → D →L[ℂ] E} {s : Set ℝ} {n : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K s) (hsa : ∀ t ∈ s, domain.IsSelfAdjoint (K t))
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∈ domain.resolventSet (K t)) :
    ContDiffOn ℝ n (fun t => domain.rieszProjection (K t) c r) s := by
  have hL := domain.contDiffOn_rieszProjectionLift hK hsa hr hgap
  have hp := (((ContinuousLinearMap.compL ℂ E D E domain.inclusion).restrictScalars ℝ).contDiff).comp_contDiffOn hL
  exact hp.congr (fun t ht => (domain.inclusion_rieszProjectionLift (K t) (hsa t ht)
    hr (hgap t ht)).symm)

end CommonDomain

end Adiabatic.Unbounded
