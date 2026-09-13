import Adiabatic.Infinite.RieszProjection
import Adiabatic.Projection
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Solving the adiabatic commutator equation by a resolvent contour

The spectral gap is expressed by a fixed isolating circle in the resolvent set.
The constructed solution needs no eigenbasis and works in arbitrary dimension.
-/

noncomputable section

namespace Adiabatic.Infinite

open Complex Metric Set
open scoped Classical

variable {A : Type*} [CStarAlgebra A]

theorem circleIntegralCLM_mul_left (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, A)) :
    circleIntegralCLM c r hr (ContinuousMap.const _ a * f) = a * circleIntegralCLM c r hr f := by
  rw [circleIntegralCLM_apply, circleIntegralCLM_apply]
  have he : (∮ z in C(c, r), circleExtension (ContinuousMap.const _ a * f) z) =
      (∮ z in C(c, r), (ContinuousLinearMap.mul ℂ A a) (circleExtension f z)) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    simp only [circleExtension, dif_pos hz, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      ContinuousLinearMap.mul_apply']
  rw [he, circleIntegral_comp_comm _ ((continuousOn_circleExtension f).circleIntegrable hr)]
  rfl

theorem circleIntegralCLM_mul_right (a : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, A)) :
    circleIntegralCLM c r hr (f * ContinuousMap.const _ a) = circleIntegralCLM c r hr f * a := by
  rw [circleIntegralCLM_apply, circleIntegralCLM_apply]
  have he : (∮ z in C(c, r), circleExtension (f * ContinuousMap.const _ a) z) =
      (∮ z in C(c, r), (ContinuousLinearMap.mul ℂ A).flip a (circleExtension f z)) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    simp only [circleExtension, dif_pos hz, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  rw [he, circleIntegral_comp_comm _ ((continuousOn_circleExtension f).circleIntegrable hr)]
  rfl

theorem resolvent_sandwich_commutator {a : A} {z : ℂ} (hz : z ∉ spectrum ℂ a) (b : A) :
    a * (resolvent a z * b * resolvent a z) - (resolvent a z * b * resolvent a z) * a =
      resolvent a z * b - b * resolvent a z := by
  have hu : IsUnit (algebraMap ℂ A z - a) := spectrum.notMem_iff.mp hz
  have hleft : a * resolvent a z = z • resolvent a z - 1 := by
    have h := Ring.mul_inverse_cancel _ hu
    change (algebraMap ℂ A z - a) * resolvent a z = 1 at h
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
  have hright : resolvent a z * a = z • resolvent a z - 1 := by
    have h := Ring.inverse_mul_cancel _ hu
    change resolvent a z * (algebraMap ℂ A z - a) = 1 at h
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
  calc
    a * (resolvent a z * b * resolvent a z) - (resolvent a z * b * resolvent a z) * a =
        (a * resolvent a z) * b * resolvent a z -
          resolvent a z * b * (resolvent a z * a) := by noncomm_ring
    _ = resolvent a z * b - b * resolvent a z := by
      rw [hleft, hright]
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      abel

/-- The resolvent sandwich, in the fixed Banach algebra of contour functions. -/
def contourSandwich (a b : A) (c : ℂ) (r : ℝ) : C(sphere c r, A) :=
  Ring.inverse (contourShift c r a) * ContinuousMap.const _ b * Ring.inverse (contourShift c r a)

/-- A contour construction solving the commutator equation with the selected projection. -/
def contourCommutator (a b : A) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : A :=
  (-contourNormalization) • circleIntegralCLM c r hr (contourSandwich a b c r)

/-- A genuine resolvent gap supplies the inverse commutator needed for adiabatic transport. -/
theorem contourCommutator_commutator {a : A} (b : A) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ z ∈ sphere c r, z ∉ spectrum ℂ a) :
    a * contourCommutator a b c r hr - contourCommutator a b c r hr * a =
      b * rieszProjection a c r - rieszProjection a c r * b := by
  have he : ContinuousMap.const _ a * contourSandwich a b c r -
      contourSandwich a b c r * ContinuousMap.const _ a =
      Ring.inverse (contourShift c r a) * ContinuousMap.const _ b -
        ContinuousMap.const _ b * Ring.inverse (contourShift c r a) := by
    ext z
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      contourSandwich, contourShift_inverse_apply hgap]
    exact resolvent_sandwich_commutator (hgap z z.property) b
  have hi := congrArg (circleIntegralCLM c r hr) he
  simp only [map_sub, circleIntegralCLM_mul_left, circleIntegralCLM_mul_right] at hi
  rw [contourCommutator, rieszProjection_eq_contourInverse hr hgap]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← smul_sub, hi, neg_smul, ← smul_neg, neg_sub, smul_sub]

/-- The contour inverse is smooth in a smooth operator path with a common resolvent contour. -/
theorem contDiffOn_contourInverse {H : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H s) {c : ℂ} {r : ℝ}
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    ContDiffOn ℝ n (fun t => Ring.inverse (contourShift c r (H t))) s := by
  have hL : ContDiffOn ℝ n (fun t => contourShift c r (H t)) s :=
    (contDiff_contourShift c r).comp_contDiffOn hH
  intro t ht
  obtain ⟨u, hu⟩ := contourShift_isUnit (hgap t ht)
  have hi := contDiffAt_ringInverse (n := n) ℝ u
  rw [hu] at hi
  exact hi.comp_contDiffWithinAt t (hL t ht)

/-- The constructed commutator solution inherits smoothness from its operator paths. -/
theorem contDiffOn_contourCommutator {H B : ℝ → A} {s : Set ℝ} {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H s) (hB : ContDiffOn ℝ n B s) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    ContDiffOn ℝ n (fun t => contourCommutator (H t) (B t) c r hr) s := by
  have hi := contDiffOn_contourInverse hH hgap
  have hb : ContDiffOn ℝ n (fun t => ContinuousMap.const (sphere c r) (B t)) s :=
    (ContinuousLinearMap.const ℝ (M := A) (sphere c r)).contDiff.comp_contDiffOn hB
  have hs : ContDiffOn ℝ n (fun t => contourSandwich (H t) (B t) c r) s :=
    (hi.mul hb).mul hi
  exact ContDiffOn.const_smul (-contourNormalization)
    (((circleIntegralCLM (E := A) c r hr).restrictScalars ℝ).contDiff.comp_contDiffOn hs)

end Adiabatic.Infinite
