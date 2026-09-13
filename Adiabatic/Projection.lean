import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.NoncommRing

/-!
# Differentiable projection calculus

These are the elementary identities behind Kato's parallel transport for a differentiable
family of projections: differentiating `P² = P` makes `P'` off diagonal, and the commutator
`K = P' P - P P'` satisfies `K P - P K = P'`.

The algebraic statements apply to arbitrary rings. The analytic statements derive their
hypotheses from actual derivatives in normed real algebras, including endpoint derivatives
within a set. This file does not construct spectral projections or a transport propagator.

Mathematical source: T. Kato, *On the adiabatic theorem of quantum mechanics* (1950).
-/

namespace Adiabatic

section Algebra

variable {A : Type*} [Ring A]

/-- The generator of Kato transport, with the convention `V' = K V`. -/
def katoGenerator (P dP : A) : A :=
  dP * P - P * dP

/-- Differentiating an idempotent makes its derivative vanish between two copies of it. -/
theorem projection_sandwich_eq_zero {P dP : A} (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) : P * dP * P = 0 := by
  have h : P * dP * P + P * dP = P * dP := by
    simpa only [mul_add, ← mul_assoc, hP] using congrArg (P * ·) hdP
  exact add_right_cancel (h.trans (zero_add (P * dP)).symm)

/-- Kato's generator transports the projection infinitesimally. -/
theorem katoGenerator_commutator {P dP : A} (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    katoGenerator P dP * P - P * katoGenerator P dP = dP := by
  have hzero := projection_sandwich_eq_zero hP hdP
  calc
    katoGenerator P dP * P - P * katoGenerator P dP =
        dP * (P * P) - P * dP * P - P * dP * P + (P * P) * dP := by
      unfold katoGenerator
      noncomm_ring
    _ = dP * P + P * dP := by rw [hP, hzero]; simp
    _ = dP := hdP

/-- The complementary projection also has a vanishing derivative sandwich. -/
theorem complement_projection_sandwich_eq_zero {P dP : A} (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) : (1 - P) * dP * (1 - P) = 0 := by
  have hzero := projection_sandwich_eq_zero hP hdP
  calc
    (1 - P) * dP * (1 - P) = dP - (dP * P + P * dP) + P * dP * P := by
      noncomm_ring
    _ = 0 := by rw [hdP, hzero]; simp

variable [StarRing A]

/-- For self-adjoint inputs the transport generator is skew-adjoint. -/
theorem star_katoGenerator {P dP : A} (hP : star P = P) (hdP : star dP = dP) :
    star (katoGenerator P dP) = -katoGenerator P dP := by
  simp only [katoGenerator, star_sub, star_mul, hP, hdP, neg_sub]

end Algebra

section Derivative

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {P : ℝ → A} {dP : A} {t : ℝ}

/-- The product rule applied to a differentiable family of idempotents. -/
theorem projection_derivative (hP : ∀ u, P u * P u = P u)
    (hderiv : HasDerivAt P dP t) : dP * P t + P t * dP = dP := by
  have hmul : HasDerivAt P (dP * P t + P t * dP) t := by
    simpa only [Pi.mul_def, hP] using hderiv.mul hderiv
  exact hmul.unique hderiv

/-- The derivative of a projection has no component within its range. -/
theorem projection_derivative_sandwich (hP : ∀ u, P u * P u = P u)
    (hderiv : HasDerivAt P dP t) : P t * dP * P t = 0 :=
  projection_sandwich_eq_zero (hP t) (projection_derivative hP hderiv)

/-- The commutator identity derived from differentiability, rather than assumed algebraically. -/
theorem katoGenerator_commutator_of_hasDerivAt (hP : ∀ u, P u * P u = P u)
    (hderiv : HasDerivAt P dP t) :
    katoGenerator (P t) dP * P t - P t * katoGenerator (P t) dP = dP :=
  katoGenerator_commutator (hP t) (projection_derivative hP hderiv)

variable {s : Set ℝ}

/-- A within-set version of the product rule, applicable at interval endpoints. -/
theorem projection_derivativeWithin (hP : ∀ u ∈ s, P u * P u = P u)
    (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t)
    (hderiv : HasDerivWithinAt P dP s t) : dP * P t + P t * dP = dP := by
  have hmul : HasDerivWithinAt (fun u => P u * P u)
      (dP * P t + P t * dP) s t := hderiv.mul hderiv
  exact hs.eq_deriv s (hmul.congr_of_mem (fun u hu => (hP u hu).symm) ht) hderiv

/-- Kato's commutator identity remains valid for a unique derivative within a set. -/
theorem katoGenerator_commutator_of_hasDerivWithinAt
    (hP : ∀ u ∈ s, P u * P u = P u) (ht : t ∈ s)
    (hs : UniqueDiffWithinAt ℝ s t) (hderiv : HasDerivWithinAt P dP s t) :
    katoGenerator (P t) dP * P t - P t * katoGenerator (P t) dP = dP :=
  katoGenerator_commutator (hP t ht) (projection_derivativeWithin hP ht hs hderiv)

variable [StarRing A] [StarModule ℝ A] [ContinuousStar A]

/-- A real derivative of a self-adjoint family is self-adjoint. -/
theorem star_projection_derivative (hP : ∀ u, star (P u) = P u)
    (hderiv : HasDerivAt P dP t) : star dP = dP := by
  have hstar : HasDerivAt P (star dP) t := by
    simpa only [hP] using hderiv.star
  exact hstar.unique hderiv

/-- For a differentiable self-adjoint family, Kato's generator is skew-adjoint. -/
theorem star_katoGenerator_of_hasDerivAt (hP : ∀ u, star (P u) = P u)
    (hderiv : HasDerivAt P dP t) :
    star (katoGenerator (P t) dP) = -katoGenerator (P t) dP :=
  star_katoGenerator (hP t) (star_projection_derivative hP hderiv)

/-- The real derivative within a set of a self-adjoint family is self-adjoint. -/
theorem star_projection_derivativeWithin (hP : ∀ u ∈ s, star (P u) = P u)
    (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t)
    (hderiv : HasDerivWithinAt P dP s t) : star dP = dP :=
  hs.eq_deriv s (hderiv.star.congr_of_mem (fun u hu => (hP u hu).symm) ht) hderiv

/-- The within-set version of skew-adjointness for Kato's generator. -/
theorem star_katoGenerator_of_hasDerivWithinAt (hP : ∀ u ∈ s, star (P u) = P u)
    (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t)
    (hderiv : HasDerivWithinAt P dP s t) :
    star (katoGenerator (P t) dP) = -katoGenerator (P t) dP :=
  star_katoGenerator (hP t ht) (star_projection_derivativeWithin hP ht hs hderiv)

end Derivative

end Adiabatic
