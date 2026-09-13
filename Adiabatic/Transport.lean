import Adiabatic.Projection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Intertwining for supplied Kato transport

A supplied solution of `V' = B V`, where `B` is skew-adjoint and `[B, P] = P'`, has
constant transported projection `V* P V`. If `V` is unitary, this gives the exact
intertwining identity `P(t) V(t) = V(t) P(0)`. In finite dimension, unitarity is itself
derived from the supplied evolution equation and initial value.

The Kato specialization derives the commutator and skew-adjointness conditions from a
differentiable orthogonal projection and a commuting skew-adjoint Hamiltonian term.
The interval includes both endpoints. Existence of the propagator is not asserted here.

Mathematical source: T. Kato, *On the adiabatic theorem of quantum mechanics* (1950).
-/

namespace Adiabatic

open Set

section Transport

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [StarRing A] [StarModule ℝ A] [ContinuousStar A]
variable {P V : ℝ → A} {B dP : A} {t : ℝ} {s : Set ℝ}

/-- The derivative of `V* P V` vanishes when the generator has the transport commutator. -/
theorem transported_projection_hasDerivWithinAt_zero
    (hP : HasDerivWithinAt P dP s t)
    (hV : HasDerivWithinAt V (B * V t) s t)
    (hB : star B = -B) (hcomm : B * P t - P t * B = dP) :
    HasDerivWithinAt (fun u => star (V u) * P u * V u) 0 s t := by
  have hzero : (star (B * V t) * P t + star (V t) * dP) * V t +
      (star (V t) * P t) * (B * V t) = 0 := by
    rw [star_mul, hB, ← hcomm]
    noncomm_ring
  have hd : HasDerivWithinAt (fun u => star (V u) * P u * V u)
      ((star (B * V t) * P t + star (V t) * dP) * V t +
        (star (V t) * P t) * (B * V t)) s t := (hV.star.mul hP).mul hV
  simpa only [hzero] using hd

variable {B dP : ℝ → A}

/-- The transported projection is constant along a supplied solution on `[0, 1]`. -/
theorem transported_projection_eq_initial
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP u) (Icc 0 1) u)
    (hV : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V (B u * V u) (Icc 0 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hcomm : ∀ u ∈ Icc (0 : ℝ) 1, B u * P u - P u * B u = dP u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    star (V t) * P t * V t = P 0 := by
  have hd : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun v => star (V v) * P v * V v) 0 (Icc 0 1) u :=
    fun u hu => transported_projection_hasDerivWithinAt_zero
      (hP u hu) (hV u hu) (hB u hu) (hcomm u hu)
  have hc := constant_of_derivWithin_zero
    (fun u hu => (hd u hu).differentiableWithinAt)
    (fun u hu => (hd u ⟨hu.1, hu.2.le⟩).derivWithin
      (uniqueDiffOn_Icc_zero_one u ⟨hu.1, hu.2.le⟩)) t ht
  simpa only [hV0, star_one, one_mul, mul_one] using hc

/-- A supplied solution for a skew-adjoint generator preserves its initial isometry. -/
theorem transport_star_mul_self
    (hV : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V (B u * V u) (Icc 0 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) : star (V t) * V t = 1 := by
  simpa only [mul_one] using transported_projection_eq_initial
    (P := fun _ => (1 : A)) (dP := fun _ => (0 : A))
    (fun u _ => hasDerivWithinAt_const u (Icc 0 1) 1) hV hB
    (fun _ _ => by simp) hV0 ht

/-- In finite dimension, the supplied skew-adjoint evolution is unitary. -/
theorem transport_mem_unitary_of_finiteDimensional [FiniteDimensional ℝ A]
    (hV : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V (B u * V u) (Icc 0 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) : V t ∈ unitary A := by
  have hleft := transport_star_mul_self hV hB hV0 ht
  refine Unitary.mem_iff.mpr ⟨hleft, ?_⟩
  apply Algebra.lmul_injective (R := ℝ)
  rw [map_mul, map_one]
  apply mul_eq_one_symm
  rw [← map_mul, hleft, map_one]

/-- Unitary supplied transport intertwines its initial and instantaneous projections. -/
theorem transport_intertwines
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP u) (Icc 0 1) u)
    (hV : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V (B u * V u) (Icc 0 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hcomm : ∀ u ∈ Icc (0 : ℝ) 1, B u * P u - P u * B u = dP u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) (hunitary : V t ∈ unitary A) :
    P t * V t = V t * P 0 := by
  have hc := congrArg (V t * ·) (transported_projection_eq_initial hP hV hB hcomm hV0 ht)
  simpa only [← mul_assoc, Unitary.mul_star_self_of_mem hunitary, one_mul] using hc

/-- Kato transport with an additional commuting skew-adjoint term intertwines projections. -/
theorem kato_transport_intertwines {G : ℝ → A}
    (hPid : ∀ u ∈ Icc (0 : ℝ) 1, P u * P u = P u)
    (hPstar : ∀ u ∈ Icc (0 : ℝ) 1, star (P u) = P u)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP u) (Icc 0 1) u)
    (hV : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V ((G u + katoGenerator (P u) (dP u)) * V u) (Icc 0 1) u)
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, star (G u) = -G u)
    (hcomm : ∀ u ∈ Icc (0 : ℝ) 1, G u * P u = P u * G u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) (hunitary : V t ∈ unitary A) :
    P t * V t = V t * P 0 := by
  apply transport_intertwines hP hV ?_ ?_ hV0 ht hunitary
  · intro u hu
    rw [star_add, hG u hu, star_katoGenerator_of_hasDerivWithinAt
      hPstar hu (uniqueDiffOn_Icc_zero_one u hu) (hP u hu), neg_add]
  · intro u hu
    have hK := katoGenerator_commutator_of_hasDerivWithinAt
      hPid hu (uniqueDiffOn_Icc_zero_one u hu) (hP u hu)
    calc
      (G u + katoGenerator (P u) (dP u)) * P u -
          P u * (G u + katoGenerator (P u) (dP u)) =
          (G u * P u - P u * G u) +
            (katoGenerator (P u) (dP u) * P u - P u * katoGenerator (P u) (dP u)) := by
        noncomm_ring
      _ = dP u := by rw [hcomm u hu, sub_self, zero_add, hK]

/-- In finite dimension, Kato intertwining follows from the supplied evolution equations. -/
theorem kato_transport_intertwines_of_finiteDimensional [FiniteDimensional ℝ A]
    {G : ℝ → A}
    (hPid : ∀ u ∈ Icc (0 : ℝ) 1, P u * P u = P u)
    (hPstar : ∀ u ∈ Icc (0 : ℝ) 1, star (P u) = P u)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP u) (Icc 0 1) u)
    (hV : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V ((G u + katoGenerator (P u) (dP u)) * V u) (Icc 0 1) u)
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, star (G u) = -G u)
    (hcomm : ∀ u ∈ Icc (0 : ℝ) 1, G u * P u = P u * G u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) : P t * V t = V t * P 0 := by
  apply kato_transport_intertwines hPid hPstar hP hV hG hcomm hV0 ht
  apply transport_mem_unitary_of_finiteDimensional hV ?_ hV0 ht
  intro u hu
  rw [star_add, hG u hu, star_katoGenerator_of_hasDerivWithinAt
    hPstar hu (uniqueDiffOn_Icc_zero_one u hu) (hP u hu), neg_add]

end Transport

end Adiabatic
