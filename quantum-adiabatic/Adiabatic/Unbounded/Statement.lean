import Adiabatic.Unbounded.Propagator
import Adiabatic.Unbounded.RieszProjection

/-!
# Statement of the common-domain unbounded adiabatic theorem

The hypotheses and conclusion of `Adiabatic.Unbounded.MainTheorem` are
defined here. The spectral band may move and need not have finite rank.
Its continuous boundaries remain a uniform positive distance from the
spectrum, and its projection is defined by a resolvent integral.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A twice continuously differentiable self-adjoint common-domain Hamiltonian
with a uniformly isolated, possibly moving and infinite-rank spectral band. -/
structure GappedHamiltonian (domain : CommonDomain D E) where
  H : ℝ → D →L[ℂ] E
  smooth : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1)
  selfAdjoint : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)
  lower : ℝ → ℝ
  upper : ℝ → ℝ
  lower_continuous : ContinuousOn lower (Icc (0 : ℝ) 1)
  upper_continuous : ContinuousOn upper (Icc (0 : ℝ) 1)
  band_ordered : ∀ t ∈ Icc (0 : ℝ) 1, lower t < upper t
  gap : ℝ
  gap_positive : 0 < gap
  spectral_gap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ domain.spectrum (H t),
    gap ≤ ‖w - (lower t : ℂ)‖ ∧ gap ≤ ‖w - (upper t : ℂ)‖

namespace GappedHamiltonian

variable {domain : CommonDomain D E}

/-- The band's spectral projection, constructed from its enclosing circle. -/
def spectralProjection (data : GappedHamiltonian domain) (t : ℝ) : E →L[ℂ] E :=
  domain.rieszProjection (data.H t) (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
    ((data.upper t - data.lower t) / 2)

/-- The quantitative gap puts the enclosing circle in the resolvent
set, including its two real endpoints. -/
theorem enclosing_circle_resolvent (data : GappedHamiltonian domain)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ w ∈ Metric.sphere (((data.lower t + data.upper t) / 2 : ℝ) : ℂ)
      ((data.upper t - data.lower t) / 2), w ∈ domain.resolventSet (data.H t) := by
  intro w hw
  by_contra hn
  have hspec : w ∈ domain.spectrum (data.H t) := hn
  have him := domain.spectrum_im_eq_zero (data.H t) (data.selfAdjoint t ht) hspec
  have hre : w = (w.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hd : |w.re - (data.lower t + data.upper t) / 2| =
      (data.upper t - data.lower t) / 2 := by
    rw [hre] at hw
    simpa only [Metric.mem_sphere, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hw
  have heither : w.re = data.lower t ∨ w.re = data.upper t := by
    rcases le_total 0 (w.re - (data.lower t + data.upper t) / 2) with hp | hm
    · rw [abs_of_nonneg hp] at hd
      right
      linarith
    · rw [abs_of_nonpos hm] at hd
      left
      linarith
  obtain ⟨hlo, hhi⟩ := data.spectral_gap t ht w hspec
  rcases heither with hlo' | hhi'
  · rw [hre, hlo', sub_self, norm_zero] at hlo
    exact (not_le_of_gt data.gap_positive) hlo
  · rw [hre, hhi', sub_self, norm_zero] at hhi
    exact (not_le_of_gt data.gap_positive) hhi

/-- The moving band's constructed contour projection is orthogonal. -/
theorem spectralProjection_isStarProjection (data : GappedHamiltonian domain)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    data.spectralProjection t * data.spectralProjection t = data.spectralProjection t ∧
      star (data.spectralProjection t) = data.spectralProjection t := by
  apply domain.rieszProjection_isStarProjection (data.H t) (data.selfAdjoint t ht)
    (show 0 < (data.upper t - data.lower t) / 2 by linarith [data.band_ordered t ht])
    (data.enclosing_circle_resolvent ht)

end GappedHamiltonian

/-- The common-domain theorem: derive smooth orthogonal band projections,
construct strong Schrödinger evolution, and prove a uniform operator-norm
adiabatic estimate. Its proof is `common_domain_adiabatic_theorem`. -/
def CommonDomainAdiabaticTheorem (domain : CommonDomain D E) : Prop :=
  ∀ data : GappedHamiltonian domain,
    (ContDiffOn ℝ 2 data.spectralProjection (Icc (0 : ℝ) 1)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      data.spectralProjection t * data.spectralProjection t = data.spectralProjection t ∧
      star (data.spectralProjection t) = data.spectralProjection t) ∧
    (∀ T : ℝ, 0 < T →
      Nonempty (StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)))) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ∀ U : StrongPropagator domain data.H (fun _ => 0) (-Complex.I * (T : ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖U.evolution t * data.spectralProjection 0 * star (U.evolution t) -
          data.spectralProjection t‖ ≤ C / T ∧
        ‖(1 - data.spectralProjection t) * U.evolution t * data.spectralProjection 0‖ ≤ C / T

end Adiabatic.Unbounded
