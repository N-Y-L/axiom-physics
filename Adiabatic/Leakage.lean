import Adiabatic.Bounds
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# From comparison to spectral leakage

Orthogonal projections are contractions. Exact intertwining for the comparison
evolution therefore turns its norm-distance bound into a leakage bound.
-/

namespace Adiabatic

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- An orthogonal projection has norm at most one. -/
theorem norm_projection_le_one (P : A) (hid : P * P = P) (hstar : star P = P) :
    ‖P‖ ≤ 1 := by
  have hnorm : ‖P‖ = ‖P‖ * ‖P‖ := by
    simpa only [hstar, hid] using (CStarRing.norm_star_mul_self (x := P))
  nlinarith [norm_nonneg P]

/-- The orthogonal complement projection also has norm at most one. -/
theorem norm_complement_projection_le_one (P : A)
    (hid : P * P = P) (hstar : star P = P) : ‖1 - P‖ ≤ 1 := by
  apply norm_projection_le_one
  · calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hid]; abel
  · simp only [star_sub, star_one, hstar]

/-- Exact transport of the selected subspace controls physical leakage by
the norm distance between the physical and comparison evolutions. -/
theorem leakage_le_comparison (P P₀ U V : A)
    (hP : P * P = P) (hPstar : star P = P)
    (hP₀ : P₀ * P₀ = P₀) (hP₀star : star P₀ = P₀)
    (hintertwines : P * V = V * P₀) :
    ‖(1 - P) * U * P₀‖ ≤ ‖U - V‖ := by
  have hzero : (1 - P) * V * P₀ = 0 := by
    rw [mul_assoc, ← hintertwines, ← mul_assoc, sub_mul, one_mul, hP,
      sub_self, zero_mul]
  calc
    ‖(1 - P) * U * P₀‖ = ‖(1 - P) * (U - V) * P₀‖ := by
      have hsplit : (1 - P) * (U - V) * P₀ =
          (1 - P) * U * P₀ - (1 - P) * V * P₀ := by noncomm_ring
      rw [hsplit, hzero, sub_zero]
    _ ≤ ‖U - V‖ := norm_contraction_mul _ _ _
      (norm_complement_projection_le_one P hP hPstar)
      (norm_projection_le_one P₀ hP₀ hP₀star)

end Adiabatic
