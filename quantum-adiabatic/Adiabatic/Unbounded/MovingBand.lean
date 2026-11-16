import Adiabatic.Unbounded.Statement
import Adiabatic.Unbounded.ContourIndependence

/-!
# Local contours for moving spectral bands

A continuous choice of band boundaries need not itself be differentiable.
The uniform spectral gap makes its selected spectrum locally unchanged
when the boundaries are held fixed. This supplies local fixed contours
for differentiating the resolvent projection.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Filter Metric
open scoped Topology

/-- Moving a boundary by less than its spectral distance preserves the
side of that boundary on which a spectral value lies. -/
theorem threshold_lt_stable {a a₀ x g : ℝ}
    (hmove : |a - a₀| < g) (hgap : g ≤ |x - a|) :
    (a < x ↔ a₀ < x) := by
  have hm := abs_lt.mp hmove
  by_cases hax : a < x
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - a)] at hgap
    constructor <;> intro <;> linarith
  · have hxa : x ≤ a := le_of_not_gt hax
    rw [abs_of_nonpos (by linarith : x - a ≤ 0)] at hgap
    constructor <;> intro <;> linarith

/-- The corresponding stability for an upper band boundary. -/
theorem lt_threshold_stable {b b₀ x g : ℝ}
    (hmove : |b - b₀| < g) (hgap : g ≤ |x - b|) :
    (x < b ↔ x < b₀) := by
  have h := threshold_lt_stable (a := -b) (a₀ := -b₀) (x := -x) (g := g)
    (by simpa only [neg_sub_neg, abs_sub_comm] using hmove)
    (by simpa only [neg_sub_neg, abs_sub_comm] using hgap)
  simpa only [neg_lt_neg_iff] using h

/-- A real spectral interval is the intersection of a circle's disk with
the real line. -/
theorem real_mem_enclosing_disk {a b x : ℝ} :
    (x : ℂ) ∈ ball (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2) ↔ a < x ∧ x < b := by
  simp only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A real point on the enclosing circle is one of the interval's endpoints. -/
theorem real_mem_enclosing_sphere {a b x : ℝ}
    (hx : (x : ℂ) ∈ sphere (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2)) :
    x = a ∨ x = b := by
  have hd : |x - (a + b) / 2| = (b - a) / 2 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hx
  rcases le_total 0 (x - (a + b) / 2) with hp | hm
  · rw [abs_of_nonneg hp] at hd
    right
    linarith
  · rw [abs_of_nonpos hm] at hd
    left
    linarith

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E}

omit [CompleteSpace D] in
/-- Continuous moving endpoints stay closer than the gap to their values
at a fixed time, on a relative neighborhood of that time. -/
theorem GappedHamiltonian.eventually_boundaries_close
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ u in 𝓝[Icc (0 : ℝ) 1] t,
      |data.lower u - data.lower t| < data.gap ∧
        |data.upper u - data.upper t| < data.gap := by
  have hl := (data.lower_continuous t ht).tendsto.eventually
    (Metric.ball_mem_nhds (data.lower t) data.gap_positive)
  have hu := (data.upper_continuous t ht).tendsto.eventually
    (Metric.ball_mem_nhds (data.upper t) data.gap_positive)
  filter_upwards [hl, hu] with u hlu huu
  simpa only [Metric.mem_ball, Real.dist_eq] using And.intro hlu huu

/-- A circle with real endpoints in the resolvent set avoids the entire
spectrum of a self-adjoint operator. -/
theorem CommonDomain.enclosing_circle_resolvent_of_endpoints
    (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H) {a b : ℝ}
    (ha : (a : ℂ) ∈ domain.resolventSet H) (hb : (b : ℂ) ∈ domain.resolventSet H) :
    ∀ w ∈ sphere (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2),
      w ∈ domain.resolventSet H := by
  intro w hw
  by_contra hn
  have hspec : w ∈ domain.spectrum H := hn
  have him := domain.spectrum_im_eq_zero H hH hspec
  have hre : w = (w.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  rw [hre] at hw hn
  rcases real_mem_enclosing_sphere hw with hwa | hwb
  · exact hn (hwa ▸ ha)
  · exact hn (hwb ▸ hb)

/-- Close band boundaries give a fixed circle in the current resolvent set. -/
theorem GappedHamiltonian.fixed_circle_resolvent_of_close
    (data : GappedHamiltonian domain) {t u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hclose : |data.lower u - data.lower t| < data.gap ∧
      |data.upper u - data.upper t| < data.gap) :
    ∀ w ∈ sphere (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
      ((data.upper t - data.lower t) / 2), w ∈ domain.resolventSet (data.H u) := by
  apply CommonDomain.enclosing_circle_resolvent_of_endpoints (data.H u) (data.selfAdjoint u hu)
  · by_contra hn
    have hg := (data.spectral_gap u hu (data.lower t : ℂ) hn).1
    have hn' : data.gap ≤ |data.lower u - data.lower t| := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using hg
    exact (not_le_of_gt hclose.1) hn'
  · by_contra hn
    have hg := (data.spectral_gap u hu (data.upper t : ℂ) hn).2
    have hn' : data.gap ≤ |data.upper u - data.upper t| := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using hg
    exact (not_le_of_gt hclose.2) hn'

/-- Close boundaries select exactly the same portion of the current spectrum. -/
theorem GappedHamiltonian.disk_membership_stable
    (data : GappedHamiltonian domain) {t u : ℝ}
    (_ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hclose : |data.lower u - data.lower t| < data.gap ∧
      |data.upper u - data.upper t| < data.gap)
    {w : ℂ} (hw : w ∈ domain.spectrum (data.H u)) :
    (w ∈ ball (((data.lower u + data.upper u) / 2 : ℝ) : ℂ)
      ((data.upper u - data.lower u) / 2) ↔
    w ∈ ball (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
      ((data.upper t - data.lower t) / 2)) := by
  have him := domain.spectrum_im_eq_zero (data.H u) (data.selfAdjoint u hu) hw
  have hre : w = (w.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  obtain ⟨hlo, hhi⟩ := data.spectral_gap u hu w hw
  rw [hre] at hlo hhi ⊢
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlo hhi
  rw [real_mem_enclosing_disk, real_mem_enclosing_disk]
  exact and_congr (threshold_lt_stable hclose.1 hlo) (lt_threshold_stable hclose.2 hhi)

/-- The moving projection locally agrees with the projection from a fixed
circle, even though the endpoints are only continuous. -/
theorem GappedHamiltonian.eventually_spectralProjection_eq_fixed
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ u in 𝓝[Icc (0 : ℝ) 1] t,
      data.spectralProjection u =
        domain.rieszProjection (data.H u) (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
          ((data.upper t - data.lower t) / 2) := by
  filter_upwards [self_mem_nhdsWithin, data.eventually_boundaries_close ht] with u hu hc
  exact domain.rieszProjection_eq_of_spectral_membership (data.H u) (data.selfAdjoint u hu)
    (show 0 < (data.upper u - data.lower u) / 2 by linarith [data.band_ordered u hu])
    (show 0 < (data.upper t - data.lower t) / 2 by linarith [data.band_ordered t ht])
    (data.enclosing_circle_resolvent hu) (data.fixed_circle_resolvent_of_close hu hc)
    (fun _ hw => data.disk_membership_stable ht hu hc hw)

/-- The constructed projection of a continuously moving, uniformly isolated
spectral band inherits the Hamiltonian's twice continuous differentiability. -/
theorem GappedHamiltonian.spectralProjection_contDiff (data : GappedHamiltonian domain) :
    ContDiffOn ℝ 2 data.spectralProjection (Icc (0 : ℝ) 1) := by
  intro t ht
  let S : Set ℝ := {u | u ∈ Icc (0 : ℝ) 1 ∧
    |data.lower u - data.lower t| < data.gap ∧
    |data.upper u - data.upper t| < data.gap}
  have hS : S ∈ 𝓝[Icc (0 : ℝ) 1] t := by
    filter_upwards [self_mem_nhdsWithin, data.eventually_boundaries_close ht] with u hu hc
    exact ⟨hu, hc⟩
  have htS : t ∈ S := ⟨ht, by simpa using And.intro data.gap_positive data.gap_positive⟩
  have hfix : ContDiffOn ℝ 2
      (fun u => domain.rieszProjection (data.H u)
        (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
        ((data.upper t - data.lower t) / 2)) S :=
    domain.contDiffOn_rieszProjection (data.smooth.mono (fun _ hu => hu.1))
      (fun u hu => data.selfAdjoint u hu.1)
      (show 0 ≤ (data.upper t - data.lower t) / 2 by linarith [data.band_ordered t ht])
      (fun u hu => data.fixed_circle_resolvent_of_close hu.1 hu.2)
  exact ((hfix t htS).mono_of_mem_nhdsWithin hS).congr_of_eventuallyEq
    (data.eventually_spectralProjection_eq_fixed ht) rfl

/-- A total choice of the moving spectral projection's domain lift.
Only the values on the unit interval are used. -/
def GappedHamiltonian.spectralProjectionLift (data : GappedHamiltonian domain) (t : ℝ) :
    E →L[ℂ] D :=
  if hr : 0 ≤ (data.upper t - data.lower t) / 2 then
    domain.rieszProjectionLift (data.H t) (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
      ((data.upper t - data.lower t) / 2) hr
  else 0

/-- The domain-valued projection includes to the physical projection. -/
theorem GappedHamiltonian.inclusion_spectralProjectionLift
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    domain.inclusion.comp (data.spectralProjectionLift t) = data.spectralProjection t := by
  have hr : 0 ≤ (data.upper t - data.lower t) / 2 := by linarith [data.band_ordered t ht]
  rw [spectralProjectionLift, dif_pos hr]
  exact domain.inclusion_rieszProjectionLift (data.H t) (data.selfAdjoint t ht)
    hr (data.enclosing_circle_resolvent ht)

/-- Domain lifts also agree locally with their fixed-contour versions. -/
theorem GappedHamiltonian.eventually_spectralProjectionLift_eq_fixed
    (data : GappedHamiltonian domain) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : 0 ≤ (data.upper t - data.lower t) / 2) :
    ∀ᶠ u in 𝓝[Icc (0 : ℝ) 1] t,
      data.spectralProjectionLift u =
        domain.rieszProjectionLift (data.H u) (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
          ((data.upper t - data.lower t) / 2) hr := by
  filter_upwards [self_mem_nhdsWithin, data.eventually_boundaries_close ht] with u hu hc
  have hru : 0 < (data.upper u - data.lower u) / 2 := by linarith [data.band_ordered u hu]
  rw [spectralProjectionLift, dif_pos hru.le]
  exact domain.rieszProjectionLift_eq_of_spectral_membership (data.H u) (data.selfAdjoint u hu)
    hru (show 0 < (data.upper t - data.lower t) / 2 by linarith [data.band_ordered t ht])
    (data.enclosing_circle_resolvent hu) (data.fixed_circle_resolvent_of_close hu hc)
    (fun _ hw => data.disk_membership_stable ht hu hc hw)

/-- The moving spectral projection is twice differentiable even in the
common-domain norm. -/
theorem GappedHamiltonian.spectralProjectionLift_contDiff (data : GappedHamiltonian domain) :
    ContDiffOn ℝ 2 data.spectralProjectionLift (Icc (0 : ℝ) 1) := by
  intro t ht
  let S : Set ℝ := {u | u ∈ Icc (0 : ℝ) 1 ∧
    |data.lower u - data.lower t| < data.gap ∧
    |data.upper u - data.upper t| < data.gap}
  have hS : S ∈ 𝓝[Icc (0 : ℝ) 1] t := by
    filter_upwards [self_mem_nhdsWithin, data.eventually_boundaries_close ht] with u hu hc
    exact ⟨hu, hc⟩
  have htS : t ∈ S := ⟨ht, by simpa using And.intro data.gap_positive data.gap_positive⟩
  have hr : 0 ≤ (data.upper t - data.lower t) / 2 := by linarith [data.band_ordered t ht]
  have hfix : ContDiffOn ℝ 2
      (fun u => domain.rieszProjectionLift (data.H u)
        (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
        ((data.upper t - data.lower t) / 2) hr) S :=
    domain.contDiffOn_rieszProjectionLift (data.smooth.mono (fun _ hu => hu.1))
      (fun u hu => data.selfAdjoint u hu.1) hr
      (fun u hu => data.fixed_circle_resolvent_of_close hu.1 hu.2)
  apply ((hfix t htS).mono_of_mem_nhdsWithin hS).congr_of_eventuallyEq
    (data.eventually_spectralProjectionLift_eq_fixed ht hr)
  simp only [spectralProjectionLift, dif_pos hr]

end Adiabatic.Unbounded
