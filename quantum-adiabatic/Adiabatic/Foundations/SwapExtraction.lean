import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Complex.Basic

/-!
# Extracting a bounded inverse from a quarter-turn domain lift

For the constant swap Hamiltonian on two Hilbert copies, evolution at a
quarter turn sends `(0,y)` to `(-I • y,0)`. The first component of its bounded
domain lift therefore gives a bounded inverse of the original inclusion.
This file proves the extraction step; it does not assume or establish the
existence of that evolution, nor a set-theoretic choice principle.
-/

namespace Adiabatic.Foundations

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The candidate inverse extracted from a quarter-turn lift. -/
noncomputable def inverseFromSwapLift (L : (D × E) →L[ℂ] (D × E)) : E →L[ℂ] D :=
  Complex.I • ((ContinuousLinearMap.fst ℂ D E).comp
    (L.comp (ContinuousLinearMap.inr ℂ D E)))

/-- The swap identity makes the extracted bounded map a right inverse. -/
theorem inverseFromSwapLift_right (j : D →L[ℂ] E)
    (L : (D × E) →L[ℂ] (D × E))
    (hL : ∀ y : E, j (L (0, y)).1 = -Complex.I • y) (y : E) :
    j (inverseFromSwapLift L y) = y := by
  change j (Complex.I • (L (0, y)).1) = y
  rw [map_smul, hL, smul_smul]
  simp

/-- Injectivity gives the other inverse identity without selecting preimages. -/
theorem inverseFromSwapLift_left (j : D →L[ℂ] E)
    (hj : Function.Injective j) (L : (D × E) →L[ℂ] (D × E))
    (hL : ∀ y : E, j (L (0, y)).1 = -Complex.I • y) (x : D) :
    inverseFromSwapLift L (j x) = x := by
  apply hj
  exact inverseFromSwapLift_right j L hL (j x)

/-- A concrete analytic consequence of a bounded quarter-turn domain lift. -/
theorem bounded_inverse_of_swap_lift (j : D →L[ℂ] E)
    (hj : Function.Injective j) (L : (D × E) →L[ℂ] (D × E))
    (hL : ∀ y : E, j (L (0, y)).1 = -Complex.I • y) :
    ∃ R : E →L[ℂ] D, (∀ y, j (R y) = y) ∧ (∀ x, R (j x) = x) := by
  exact ⟨inverseFromSwapLift L, inverseFromSwapLift_right j L hL,
    inverseFromSwapLift_left j hj L hL⟩

end Adiabatic.Foundations
