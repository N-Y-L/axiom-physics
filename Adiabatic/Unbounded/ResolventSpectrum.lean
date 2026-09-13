import Adiabatic.Unbounded.RieszProjection

/-!
# Spectrum of a bounded reference resolvent

A bounded rational pencil detects the unbounded resolvent set. Nonzero
spectral values of a reference resolvent therefore recover unbounded spectral
values by reciprocal translation.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E)

/-- A bounded rational pencil characterizes every point of the full resolvent set. -/
theorem rationalPencil_isUnit_iff {p z : ℂ} (hp : p ∈ domain.resolventSet H) :
    IsUnit ((z - p) • domain.physicalInverseShift H p - 1) ↔ z ∈ domain.resolventSet H := by
  refine ⟨?_, domain.rationalPencil_isUnit H hp⟩
  intro h
  rw [domain.rationalPencil_eq H hp z] at h
  have hu : IsUnit ((domain.shift H z).comp (domain.inverseShift H p)) := by simpa using h
  have hi : Function.Bijective (domain.inverseShift H p) := by
    rw [domain.inverseShift_eq H p hp]
    exact (domain.resolventAtEquiv H p hp).symm.bijective
  exact (hi.of_comp_iff (domain.shift H z)).mp (ContinuousLinearMap.isUnit_iff_bijective.mp hu)

/-- Every nonzero spectral value of a reference resolvent determines an unbounded spectral value. -/
theorem mem_spectrum_of_mem_resolvent_spectrum (hH : domain.IsSelfAdjoint H)
    (p : ℂ) (hp : p.im ≠ 0) {w : ℂ}
    (hw : w ∈ _root_.spectrum ℂ (domain.physicalInverseShift H p)) (hw0 : w ≠ 0) :
    p + w⁻¹ ∈ domain.spectrum H := by
  intro hz
  have hn := domain.physicalInverseShift_isStarNormal H hH p hp
  have hu := domain.rationalPencil_isUnit H
    (domain.mem_resolventSet_of_im_ne_zero H hH p hp) hz
  have hne := rational_denominator_ne_zero hn hu hw
  apply hne
  field_simp
  ring

end Adiabatic.Unbounded.CommonDomain
