import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Spectral projections from a fixed isolating circle

The contour integral construction works on a Hilbert space of arbitrary dimension.
The circle must lie in the resolvent set. The selected spectrum is its interior.
-/

noncomputable section

namespace Adiabatic.Infinite

open Complex Metric Set Topology
open scoped Interval Classical

/-- The normalization for a positively oriented complex contour integral. -/
def contourNormalization : ℂ := (2 * Real.pi * Complex.I)⁻¹

theorem contourNormalization_mul :
    contourNormalization * (2 * Real.pi * Complex.I) = 1 := by
  unfold contourNormalization
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

/-- The characteristic function of the interior of a circle. -/
def diskIndicator (c : ℂ) (r : ℝ) (z : ℂ) : ℂ := if z ∈ ball c r then 1 else 0

theorem normalized_circle_integral_resolvent {c w : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : w ∉ sphere c r) :
    contourNormalization * (∮ z in C(c, r), (z - w)⁻¹) = diskIndicator c r w := by
  by_cases hin : w ∈ ball c r
  · rw [circleIntegral.integral_sub_inv_of_mem_ball hin, contourNormalization_mul,
      diskIndicator, if_pos hin]
  · have hout : r < dist w c := by
      simp only [mem_ball, not_lt] at hin
      simp only [mem_sphere] at hw
      exact lt_of_le_of_ne hin (Ne.symm hw)
    have hz : ∀ z ∈ closedBall c r, z - w ≠ 0 := by
      intro z hz hzw
      have hzw' : z = w := sub_eq_zero.mp hzw
      subst z
      exact (not_le_of_gt hout) hz
    have hd : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (closedBall c r) := by
      intro z hz'
      exact ((differentiableAt_id.sub_const w).inv (hz z hz')).differentiableWithinAt
    have hi : (∮ z in C(c, r), (z - w)⁻¹) = 0 :=
      (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr.le
    rw [hi, mul_zero, diskIndicator, if_neg hin]

section LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A continuous complex linear map commutes with circle integration. -/
theorem circleIntegral_comp_comm (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    (∮ z in C(c, r), L (f z)) = L (∮ z in C(c, r), f z) := by
  simp only [circleIntegral, ← L.map_smul]
  exact L.intervalIntegral_comp_comm hf.out

end LinearMap

section CFC

variable {A : Type*} [CStarAlgebra A]

/-- The Riesz projection defined by a circle in the resolvent set. -/
def rieszProjection (a : A) (c : ℂ) (r : ℝ) : A :=
  contourNormalization • (∮ z in C(c, r), resolvent a z)

theorem cfc_resolvent {a : A} (ha : IsStarNormal a) {z : ℂ}
    (hz : z ∉ spectrum ℂ a) :
    cfc (fun w : ℂ => (z - w)⁻¹) a = resolvent a z := by
  have hn : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := by
    intro w hw hzw
    exact hz ((sub_eq_zero.mp hzw).symm ▸ hw)
  have hc : ContinuousOn (fun w : ℂ => z - w) (spectrum ℂ a) :=
    continuous_const.sub continuous_id |>.continuousOn
  rw [cfc_inv (fun w : ℂ => z - w) a hn hc ha]
  congr 1
  rw [cfc_sub (fun _ : ℂ => z) (fun w : ℂ => w)
      (hf := continuousOn_const) (hg := continuousOn_id),
    cfc_const z a ha, cfc_id' ℂ a ha]

theorem diskIndicator_sq (c : ℂ) (r : ℝ) (z : ℂ) :
    diskIndicator c r z * diskIndicator c r z = diskIndicator c r z := by
  unfold diskIndicator
  split_ifs <;> simp

theorem diskIndicator_star (c : ℂ) (r : ℝ) (z : ℂ) :
    star (diskIndicator c r z) = diskIndicator c r z := by
  unfold diskIndicator
  split_ifs <;> simp

theorem continuousAt_diskIndicator {c z : ℂ} {r : ℝ} (hz : z ∉ sphere c r) :
    ContinuousAt (diskIndicator c r) z := by
  by_cases hi : z ∈ ball c r
  · have he : diskIndicator c r =ᶠ[nhds z] fun _ => 1 := by
      filter_upwards [isOpen_ball.mem_nhds hi] with w hw
      exact if_pos hw
    exact continuousAt_const.congr_of_eventuallyEq he
  · have ho : r < dist z c := by
      simp only [mem_ball, not_lt] at hi
      simp only [mem_sphere] at hz
      exact lt_of_le_of_ne hi (Ne.symm hz)
    have he : diskIndicator c r =ᶠ[nhds z] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds ho]
        with w hw
      exact if_neg (not_lt_of_ge hw.le)
    exact continuousAt_const.congr_of_eventuallyEq he

theorem continuousOn_diskIndicator {a : A} {c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    ContinuousOn (diskIndicator c r) (spectrum ℂ a) := by
  intro z hz
  exact (continuousAt_diskIndicator (fun hc => hgap z hc hz)).continuousWithinAt

/-- The scalar resolvent viewed as a continuous function on the spectrum. -/
def spectralResolvent (a : A) (z : ℂ) : C(spectrum ℂ a, ℂ) :=
  ContinuousMap.mkD ((spectrum ℂ a).restrict (fun w => (z - w)⁻¹)) 0

theorem spectralResolvent_apply {a : A} {z : ℂ} (hz : z ∉ spectrum ℂ a)
    (w : spectrum ℂ a) : spectralResolvent a z w = (z - (w : ℂ))⁻¹ := by
  apply ContinuousMap.mkD_apply_of_continuousOn
  exact (continuous_const.sub continuous_id).continuousOn.inv₀
    (fun x hx hzx => hz ((sub_eq_zero.mp hzx).symm ▸ hx))

theorem continuousOn_spectralResolvent {a : A} {c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    ContinuousOn (spectralResolvent a) (sphere c r) := by
  apply ContinuousMap.continuousOn_mkD_restrict_of_uncurry
  exact (continuous_fst.sub continuous_snd).continuousOn.inv₀ (by
    rintro ⟨z, w⟩ ⟨hz, hw⟩ hzw
    change z - w = 0 at hzw
    exact hgap z hz ((sub_eq_zero.mp hzw).symm ▸ hw))

theorem cfcL_spectralResolvent {a : A} (ha : IsStarNormal a) {z : ℂ}
    (hz : z ∉ spectrum ℂ a) : cfcL ha (spectralResolvent a z) = resolvent a z := by
  rw [spectralResolvent, ← cfc_eq_cfcL_mkD _ a ha]
  exact cfc_resolvent ha hz

theorem normalized_integral_spectralResolvent {a : A} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    contourNormalization • (∮ z in C(c, r), spectralResolvent a z) =
      (⟨(spectrum ℂ a).restrict (diskIndicator c r),
        (continuousOn_diskIndicator hgap).restrict⟩ : C(spectrum ℂ a, ℂ)) := by
  have hi : CircleIntegrable (spectralResolvent a) c r :=
    (continuousOn_spectralResolvent hgap).circleIntegrable hr.le
  ext w
  change contourNormalization * (ContinuousMap.evalCLM ℂ w)
      (∮ z in C(c, r), spectralResolvent a z) = diskIndicator c r w
  rw [← circleIntegral_comp_comm _ hi]
  have he : (∮ z in C(c, r), (ContinuousMap.evalCLM ℂ w) (spectralResolvent a z)) =
      (∮ z in C(c, r), (z - (w : ℂ))⁻¹) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact spectralResolvent_apply (hgap z hz) w
  rw [he]
  exact normalized_circle_integral_resolvent hr (fun hw => hgap w hw w.property)

/-- The contour integral agrees with the spectral cutoff functional calculus. -/
theorem rieszProjection_eq_cfc {a : A} (ha : IsStarNormal a) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    rieszProjection a c r = cfc (diskIndicator c r) a := by
  have hi : CircleIntegrable (spectralResolvent a) c r :=
    (continuousOn_spectralResolvent hgap).circleIntegrable hr.le
  rw [rieszProjection]
  have he : (∮ z in C(c, r), resolvent a z) =
      (∮ z in C(c, r), cfcL ha (spectralResolvent a z)) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact (cfcL_spectralResolvent ha (hgap z hz)).symm
  rw [he, circleIntegral_comp_comm _ hi, ← (cfcL ha).map_smul,
    normalized_integral_spectralResolvent hr hgap]
  exact (cfc_eq_cfcL ha (continuousOn_diskIndicator hgap)).symm

/-- Functional calculus of a continuous spectral cutoff is an orthogonal projection. -/
theorem cfc_diskIndicator_projection (a : A) (c : ℂ) (r : ℝ)
    (hc : ContinuousOn (diskIndicator c r) (spectrum ℂ a)) :
    cfc (diskIndicator c r) a * cfc (diskIndicator c r) a = cfc (diskIndicator c r) a ∧
      star (cfc (diskIndicator c r) a) = cfc (diskIndicator c r) a := by
  constructor
  · rw [← cfc_mul _ _ _ hc hc]
    exact cfc_congr fun z _ => diskIndicator_sq c r z
  · rw [← cfc_star]
    exact cfc_congr fun z _ => diskIndicator_star c r z

/-- A fixed circle in the resolvent set gives an orthogonal spectral projection. -/
theorem rieszProjection_isStarProjection {a : A} (ha : IsStarNormal a) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    rieszProjection a c r * rieszProjection a c r = rieszProjection a c r ∧
      star (rieszProjection a c r) = rieszProjection a c r := by
  rw [rieszProjection_eq_cfc ha hr hgap]
  exact cfc_diskIndicator_projection a c r (continuousOn_diskIndicator hgap)

/-- The spectral projection commutes with its operator. -/
theorem rieszProjection_commute {a : A} (ha : IsStarNormal a) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    Commute (rieszProjection a c r) a := by
  rw [rieszProjection_eq_cfc ha hr hgap]
  exact (Commute.refl a).cfc ha.star_comm_self (diskIndicator c r)

end CFC

section CircleBanachSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Extend a function on the integration circle by zero away from that circle. -/
def circleExtension {c : ℂ} {r : ℝ} (f : C(sphere c r, E)) (z : ℂ) : E :=
  if hz : z ∈ sphere c r then f ⟨z, hz⟩ else 0

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem circleExtension_apply {c : ℂ} {r : ℝ} (f : C(sphere c r, E))
    (z : sphere c r) : circleExtension f z = f z := by
  simp only [circleExtension, dif_pos z.property]

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem continuousOn_circleExtension {c : ℂ} {r : ℝ} (f : C(sphere c r, E)) :
    ContinuousOn (circleExtension f) (sphere c r) := by
  rw [continuousOn_iff_continuous_restrict]
  simpa only [Set.restrict_def, circleExtension_apply] using f.continuous

/-- Circle integration is a continuous linear map on the Banach space of contour functions. -/
def circleIntegralCLM (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : C(sphere c r, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∮ z in C(c, r), circleExtension f z
      map_add' := by
        intro f g
        have he : (∮ z in C(c, r), circleExtension (f + g) z) =
            (∮ z in C(c, r), circleExtension f z + circleExtension g z) := by
          apply circleIntegral.integral_congr hr
          intro z hz
          simp only [circleExtension, dif_pos hz, ContinuousMap.add_apply]
        rw [he, circleIntegral.integral_add
          ((continuousOn_circleExtension f).circleIntegrable hr)
          ((continuousOn_circleExtension g).circleIntegrable hr)]
      map_smul' := by
        intro a f
        have he : (∮ z in C(c, r), circleExtension (a • f) z) =
            (∮ z in C(c, r), a • circleExtension f z) := by
          apply circleIntegral.integral_congr hr
          intro z hz
          simp only [circleExtension, dif_pos hz, ContinuousMap.smul_apply]
        rw [he, circleIntegral.integral_smul]
        rfl }
    (2 * Real.pi * r) (by
      intro f
      apply circleIntegral.norm_integral_le_of_norm_le_const hr
      intro z hz
      simpa only [circleExtension, dif_pos hz] using f.norm_coe_le_norm ⟨z, hz⟩)

omit [CompleteSpace E] in
theorem circleIntegralCLM_apply {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, E)) :
    circleIntegralCLM c r hr f = ∮ z in C(c, r), circleExtension f z := rfl

end CircleBanachSpace

section Regularity

variable {A : Type*} [CStarAlgebra A]

/-- The shifted operator as one element of the Banach algebra of circle functions. -/
def contourShift (c : ℂ) (r : ℝ) (a : A) : C(sphere c r, A) :=
  ⟨fun z => algebraMap ℂ A (z : ℂ) - a,
    ((continuous_algebraMap ℂ A).comp continuous_subtype_val).sub continuous_const⟩

theorem contDiff_contourShift (c : ℂ) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (contourShift c r : A → C(sphere c r, A)) := by
  have he : (contourShift c r : A → C(sphere c r, A)) =
      fun a => contourShift c r 0 - (ContinuousLinearMap.const ℝ (sphere c r)) a := by
    ext a z
    simp [contourShift]
  rw [he]
  exact contDiff_const.sub (ContinuousLinearMap.const ℝ (M := A) (sphere c r)).contDiff

theorem contourShift_isUnit {a : A} {c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) : IsUnit (contourShift c r a) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro z
  exact spectrum.notMem_iff.mp (hgap z z.property)

theorem contourShift_inverse_apply {a : A} {c : ℂ} {r : ℝ}
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) (z : sphere c r) :
    Ring.inverse (contourShift c r a) z = resolvent a (z : ℂ) := by
  have hu : IsUnit (algebraMap ℂ A (z : ℂ) - a) := spectrum.notMem_iff.mp (hgap z z.property)
  apply hu.mul_left_cancel
  change contourShift c r a z * Ring.inverse (contourShift c r a) z =
    (algebraMap ℂ A (z : ℂ) - a) * Ring.inverse (algebraMap ℂ A (z : ℂ) - a)
  rw [Ring.mul_inverse_cancel _ hu]
  exact ContinuousMap.congr_fun (Ring.mul_inverse_cancel _ (contourShift_isUnit hgap)) z

theorem rieszProjection_eq_contourInverse {a : A} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    rieszProjection a c r = contourNormalization •
      circleIntegralCLM c r hr (Ring.inverse (contourShift c r a)) := by
  rw [rieszProjection, circleIntegralCLM_apply]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  rw [show circleExtension (Ring.inverse (contourShift c r a)) z =
      Ring.inverse (contourShift c r a) ⟨z, hz⟩ from circleExtension_apply _ ⟨z, hz⟩]
  exact (contourShift_inverse_apply hgap ⟨z, hz⟩).symm

/-- Smooth Hamiltonians give equally smooth Riesz projections when a fixed contour
stays in the resolvent set. The projection is constructed by its contour integral. -/
theorem contDiffOn_rieszProjection {H : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H s) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    ContDiffOn ℝ n (fun t => rieszProjection (H t) c r) s := by
  have hL : ContDiffOn ℝ n (fun t => contourShift c r (H t)) s :=
    (contDiff_contourShift c r).comp_contDiffOn hH
  have hI : ContDiffOn ℝ n (fun t => Ring.inverse (contourShift c r (H t))) s := by
    intro t ht
    obtain ⟨u, hu⟩ := contourShift_isUnit (hgap t ht)
    have hi := contDiffAt_ringInverse (n := n) ℝ u
    rw [hu] at hi
    exact hi.comp_contDiffWithinAt t (hL t ht)
  have hp : ContDiffOn ℝ n (fun t => contourNormalization •
      circleIntegralCLM c r hr (Ring.inverse (contourShift c r (H t)))) s :=
    ContDiffOn.const_smul contourNormalization
      (((circleIntegralCLM (E := A) c r hr).restrictScalars ℝ).contDiff.comp_contDiffOn hI)
  exact hp.congr (fun t ht => rieszProjection_eq_contourInverse hr (hgap t ht))

end Regularity

end Adiabatic.Infinite
