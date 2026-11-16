import Adiabatic.Unbounded.Resolvent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounded self-adjoint approximations of an unbounded Hamiltonian

Resolvent regularizers are contractions and converge strongly to the identity.
Symmetric regularization therefore gives commuting bounded self-adjoint
Hamiltonians converging to the unbounded Hamiltonian on its full domain.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

open Filter Topology ComplexConjugate

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)

/-- The resolvent regularization of the identity. -/
def resolventRegularizer (z : ℂ) (hz : z.im ≠ 0) : E →L[ℂ] E :=
  (-z) • domain.physicalResolvent H hH z hz

/-- Purely imaginary resolvent regularizers are contractions. -/
theorem norm_resolventRegularizer_le (z : ℂ) (hz : z.im ≠ 0) (hre : z.re = 0) (x : E) :
    ‖domain.resolventRegularizer H hH z hz x‖ ≤ ‖x‖ := by
  have ha : 0 < |z.im| := abs_pos.mpr hz
  calc
    ‖domain.resolventRegularizer H hH z hz x‖ =
        |z.im| * ‖domain.physicalResolvent H hH z hz x‖ := by
      simp only [resolventRegularizer, ContinuousLinearMap.smul_apply, norm_smul, norm_neg,
        ← Complex.abs_im_eq_norm.mpr hre]
    _ ≤ |z.im| * (‖x‖ / |z.im|) :=
      mul_le_mul_of_nonneg_left (domain.norm_inclusion_resolvent_le H hH z hz x) ha.le
    _ = ‖x‖ := mul_div_cancel₀ _ ha.ne'

omit [CompleteSpace D] [CompleteSpace E] in
/-- Contractions converging on the common domain converge strongly everywhere. -/
theorem tendsto_of_contractions_on_domain (F : ℕ → E →L[ℂ] E)
    (hc : ∀ n x, ‖F n x‖ ≤ ‖x‖)
    (hd : ∀ x : D, Tendsto (fun n => F n (domain.inclusion x)) atTop
      (𝓝 (domain.inclusion x))) (x : E) : Tendsto (fun n => F n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := domain.dense.exists_dist_lt x (show 0 < ε / 4 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hd v) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  have heq : F n x - x = F n (x - domain.inclusion v) +
      (F n (domain.inclusion v) - domain.inclusion v) + (domain.inclusion v - x) := by
    simp only [map_sub]
    abel
  rw [dist_eq_norm, heq]
  have htriangle : ‖F n (x - domain.inclusion v) +
      (F n (domain.inclusion v) - domain.inclusion v) + (domain.inclusion v - x)‖ ≤
      ‖F n (x - domain.inclusion v)‖ + ‖F n (domain.inclusion v) - domain.inclusion v‖ +
      ‖domain.inclusion v - x‖ := norm_add₃_le
  have hf := hc n (x - domain.inclusion v)
  rw [dist_eq_norm] at hv hb
  rw [norm_sub_rev (domain.inclusion v) x] at htriangle
  linarith

/-- Resolvent regularizers converge strongly when the imaginary parameter diverges. -/
theorem tendsto_resolventRegularizer (z : ℕ → ℂ) (hz : ∀ n, (z n).im ≠ 0)
    (hre : ∀ n, (z n).re = 0)
    (hinv : Tendsto (fun n => |(z n).im|⁻¹) atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => domain.resolventRegularizer H hH (z n) (hz n) x) atTop (𝓝 x) := by
  apply domain.tendsto_of_contractions_on_domain _
    (fun n x => domain.norm_resolventRegularizer_le H hH (z n) (hz n) (hre n) x)
  intro v
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => domain.norm_regularization_sub_le H hH (z n) (hz n) v)
  simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv

/-- A nonzero imaginary spectral parameter tending to infinity. -/
def imaginaryPoint (n : ℕ) : ℂ := ((n : ℂ) + 1) * Complex.I

@[simp] theorem imaginaryPoint_re (n : ℕ) : (imaginaryPoint n).re = 0 := by
  simp [imaginaryPoint]

@[simp] theorem imaginaryPoint_im (n : ℕ) : (imaginaryPoint n).im = (n : ℝ) + 1 := by
  simp [imaginaryPoint]

theorem imaginaryPoint_im_ne_zero (n : ℕ) : (imaginaryPoint n).im ≠ 0 := by
  rw [imaginaryPoint_im]
  positivity

/-- Positive imaginary resolvent regularizers converge strongly to the identity. -/
theorem tendsto_positiveRegularizer (x : E) :
    Tendsto (fun n => domain.resolventRegularizer H hH (imaginaryPoint n)
      (imaginaryPoint_im_ne_zero n) x) atTop (𝓝 x) := by
  apply domain.tendsto_resolventRegularizer H hH imaginaryPoint imaginaryPoint_im_ne_zero
    imaginaryPoint_re _ x
  simpa only [imaginaryPoint_im, show ∀ n : ℕ, |(n : ℝ) + 1| = (n : ℝ) + 1 from fun n => abs_of_pos (by positivity),
    ← one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Negative imaginary resolvent regularizers converge strongly to the identity. -/
theorem tendsto_negativeRegularizer (x : E) :
    Tendsto (fun n => domain.resolventRegularizer H hH (conj (imaginaryPoint n))
      (by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n) x) atTop (𝓝 x) := by
  apply domain.tendsto_resolventRegularizer H hH (fun n => conj (imaginaryPoint n))
    (fun n => by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n) (fun n => by simp) _ x
  simpa only [Complex.conj_im, abs_neg, imaginaryPoint_im,
    show ∀ n : ℕ, |(n : ℝ) + 1| = (n : ℝ) + 1 from fun n => abs_of_pos (by positivity), ← one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The symmetric bounded approximation n² H (H²+n²)⁻¹, with n replaced by n+1. -/
def regularizedHamiltonian (n : ℕ) : E →L[ℂ] E :=
  (((n : ℂ) + 1) ^ 2 / 2) •
    (domain.physicalResolvent H hH (imaginaryPoint n) (imaginaryPoint_im_ne_zero n) +
      domain.physicalResolvent H hH (conj (imaginaryPoint n))
        (by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n))

/-- Symmetric resolvent regularization is self-adjoint. -/
theorem regularizedHamiltonian_selfAdjoint (n : ℕ) :
    star (domain.regularizedHamiltonian H hH n) = domain.regularizedHamiltonian H hH n := by
  simp only [regularizedHamiltonian, star_smul, star_add, physicalResolvent_star]
  simp only [star_div₀, star_pow, star_add, star_natCast, star_one, star_ofNat,
    starRingEnd_self_apply]
  congr 1
  exact add_comm _ _

/-- Every bounded approximation commutes with every physical resolvent. -/
theorem regularizedHamiltonian_commute_physicalResolvent (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (domain.regularizedHamiltonian H hH n) (domain.physicalResolvent H hH z hz) := by
  unfold regularizedHamiltonian
  exact ((domain.physicalResolvent_commute H hH _ z _ hz).add_left
    (domain.physicalResolvent_commute H hH _ z _ hz)).smul_left _

/-- The bounded self-adjoint approximations commute with one another. -/
theorem regularizedHamiltonian_commute (m n : ℕ) :
    Commute (domain.regularizedHamiltonian H hH m) (domain.regularizedHamiltonian H hH n) := by
  change Commute (domain.regularizedHamiltonian H hH m)
    ((((n : ℂ) + 1) ^ 2 / 2) •
      (domain.physicalResolvent H hH (imaginaryPoint n) (imaginaryPoint_im_ne_zero n) +
        domain.physicalResolvent H hH (conj (imaginaryPoint n))
          (by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n)))
  exact ((domain.regularizedHamiltonian_commute_physicalResolvent H hH m _ _).add_right
    (domain.regularizedHamiltonian_commute_physicalResolvent H hH m _ _)).smul_right _

/-- On the full domain, the bounded approximation is an average of regularizers. -/
theorem regularizedHamiltonian_apply_inclusion (n : ℕ) (x : D) :
    domain.regularizedHamiltonian H hH n (domain.inclusion x) = (1 / 2 : ℂ) •
      (domain.resolventRegularizer H hH (imaginaryPoint n) (imaginaryPoint_im_ne_zero n) (H x) +
        domain.resolventRegularizer H hH (conj (imaginaryPoint n))
          (by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n) (H x)) := by
  have hp := congrArg domain.inclusion
    (domain.resolvent_map H hH (imaginaryPoint n) (imaginaryPoint_im_ne_zero n) x)
  have hm := congrArg domain.inclusion
    (domain.resolvent_map H hH (conj (imaginaryPoint n))
      (by simpa only [Complex.conj_im, neg_ne_zero] using imaginaryPoint_im_ne_zero n) x)
  simp only [map_add, map_smul] at hp hm
  change domain.physicalResolvent H hH (imaginaryPoint n) _ (H x) =
    domain.inclusion x + imaginaryPoint n •
      domain.physicalResolvent H hH (imaginaryPoint n) _ (domain.inclusion x) at hp
  change domain.physicalResolvent H hH (conj (imaginaryPoint n)) _ (H x) =
    domain.inclusion x + conj (imaginaryPoint n) •
      domain.physicalResolvent H hH (conj (imaginaryPoint n)) _ (domain.inclusion x) at hm
  simp only [regularizedHamiltonian, resolventRegularizer, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, hp, hm]
  have hc : conj (imaginaryPoint n) = -imaginaryPoint n := by
    simp [imaginaryPoint]
  simp only [hc]
  have hs : imaginaryPoint n ^ 2 = -((n : ℂ) + 1) ^ 2 := by
    simp [imaginaryPoint, mul_pow, Complex.I_sq]
  match_scalars <;> ring_nf <;> simp [hs] <;> ring

/-- The bounded Hamiltonians converge to the unbounded Hamiltonian on every domain vector. -/
theorem tendsto_regularizedHamiltonian (x : D) :
    Tendsto (fun n => domain.regularizedHamiltonian H hH n (domain.inclusion x)) atTop (𝓝 (H x)) := by
  simp_rw [domain.regularizedHamiltonian_apply_inclusion H hH]
  have h := ((domain.tendsto_positiveRegularizer H hH (H x)).add
    (domain.tendsto_negativeRegularizer H hH (H x))).const_smul (1 / 2 : ℂ)
  have heq : (1 / 2 : ℂ) • (H x + H x) = H x := by module
  simpa only [heq] using h

end Adiabatic.Unbounded.CommonDomain
