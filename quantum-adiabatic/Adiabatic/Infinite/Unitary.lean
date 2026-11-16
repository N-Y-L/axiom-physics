import Adiabatic.Transport
import Adiabatic.Propagator
import Mathlib.Analysis.ODE.Gronwall

/-!
# Unitary bounded evolution in arbitrary dimension

A continuous skew-adjoint coefficient generates unitary evolution on the
whole unit interval in a complete real normed star algebra. For a supplied
solution, completeness is unnecessary. The right inverse identity follows
from Grönwall's inequality applied to `V V* - 1`, whose derivative is its
commutator with the generator. This avoids the finite-dimensional argument
that a left inverse must also be a right inverse.
-/

namespace Adiabatic

open Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [StarRing A] [StarModule ℝ A] [ContinuousStar A]
  {V B : ℝ → A} {t : ℝ}

/-- A bounded continuous skew-adjoint evolution has a right star inverse,
without any finite-dimensional hypothesis. -/
theorem transport_mul_star_self
    (hBc : ContinuousOn B (Icc (0 : ℝ) 1))
    (hV : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V (B u * V u) (Icc (0 : ℝ) 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    V t * star (V t) = 1 := by
  let Y : ℝ → A := fun u => V u * star (V u) - 1
  have hY : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt Y (B u * Y u - Y u * B u) (Icc (0 : ℝ) 1) u := by
    intro u hu
    have hd := ((hV u hu).mul (hV u hu).star).sub_const (1 : A)
    convert hd using 1
    simp only [Y, star_mul, hB u hu]
    noncomm_ring
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hBc
  have hYzero : Y t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (K := 2 * M) (f' := fun u => B u * Y u - Y u * B u)
      (fun u hu => (hY u hu).continuousWithinAt) ?_ ?_ ?_ t ht
    · intro u hu
      have hd := (hY u ⟨hu.1, hu.2.le⟩).mono (Icc_subset_Icc hu.1 le_rfl)
      rw [hasDerivWithinAt_iff_isLittleO, nhdsWithin_Icc_eq_nhdsGE hu.2] at hd
      exact hasDerivWithinAt_iff_isLittleO.mpr hd
    · simp [Y, hV0]
    · intro u hu
      calc
        ‖B u * Y u - Y u * B u‖ ≤ ‖B u * Y u‖ + ‖Y u * B u‖ := norm_sub_le _ _
        _ ≤ ‖B u‖ * ‖Y u‖ + ‖Y u‖ * ‖B u‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ M * ‖Y u‖ + ‖Y u‖ * M := by
          gcongr <;> exact hM u ⟨hu.1, hu.2.le⟩
        _ = 2 * M * ‖Y u‖ := by ring
  exact sub_eq_zero.mp hYzero

/-- Every normalized solution of a continuous skew-adjoint bounded
evolution equation is unitary, in arbitrary dimension. -/
theorem transport_mem_unitary
    (hBc : ContinuousOn B (Icc (0 : ℝ) 1))
    (hV : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V (B u * V u) (Icc (0 : ℝ) 1) u)
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) : V t ∈ unitary A :=
  Unitary.mem_iff.mpr ⟨transport_star_mul_self hV hB hV0 ht,
    transport_mul_star_self hBc hV hB hV0 ht⟩

/-- Continuous skew-adjoint bounded generators admit a normalized
unitary propagator on the entire unit interval. -/
theorem exists_unitary_propagator_unitInterval [CompleteSpace A]
    (hBc : ContinuousOn B (Icc (0 : ℝ) 1))
    (hB : ∀ u ∈ Icc (0 : ℝ) 1, star (B u) = -B u) :
    ∃ V : ℝ → A, V 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt V (B t * V t) (Icc (0 : ℝ) 1) t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, V t ∈ unitary A := by
  obtain ⟨V, hV0, hV⟩ := exists_propagator_unitInterval hBc
  exact ⟨V, hV0, hV, fun t ht => transport_mem_unitary hBc hV hB hV0 ht⟩

/-- Kato intertwining follows from continuous bounded generators and the
evolution equations in arbitrary dimension. -/
theorem kato_transport_intertwines_of_continuous {P dP G : ℝ → A}
    (hPid : ∀ u ∈ Icc (0 : ℝ) 1, P u * P u = P u)
    (hPstar : ∀ u ∈ Icc (0 : ℝ) 1, star (P u) = P u)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (dP u) (Icc 0 1) u)
    (hBc : ContinuousOn (fun u => G u + katoGenerator (P u) (dP u)) (Icc (0 : ℝ) 1))
    (hV : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt V ((G u + katoGenerator (P u) (dP u)) * V u) (Icc 0 1) u)
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, star (G u) = -G u)
    (hcomm : ∀ u ∈ Icc (0 : ℝ) 1, G u * P u = P u * G u)
    (hV0 : V 0 = 1) (ht : t ∈ Icc (0 : ℝ) 1) : P t * V t = V t * P 0 := by
  apply kato_transport_intertwines hPid hPstar hP hV hG hcomm hV0 ht
  apply transport_mem_unitary hBc hV ?_ hV0 ht
  intro u hu
  rw [star_add, hG u hu, star_katoGenerator_of_hasDerivWithinAt
    hPstar hu (uniqueDiffOn_Icc_zero_one u hu) (hP u hu), neg_add]

end Adiabatic
