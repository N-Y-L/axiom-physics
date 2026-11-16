import Adiabatic.Leakage

/-!
# Distance between transported spectral projections

Exact intertwining for a comparison evolution converts its distance from
the physical evolution into a bound for the transported projection.
-/

namespace Adiabatic

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- Unitary comparison controls the distance between the physical spectral
projection and its instantaneous target. -/
theorem projection_distance_le_comparison (P P₀ U V : A)
    (hP₀ : P₀ * P₀ = P₀) (hP₀star : star P₀ = P₀)
    (hU : U ∈ unitary A) (hV : V ∈ unitary A)
    (hinter : P * V = V * P₀) :
    ‖U * P₀ * star U - P‖ ≤ 2 * ‖U - V‖ := by
  have hPV : P = V * P₀ * star V := by
    rw [← hinter, mul_assoc, Unitary.mul_star_self_of_mem hV, mul_one]
  have hsplit : U * P₀ * star U - P =
      (U - V) * P₀ * star U + V * P₀ * (star U - star V) := by
    rw [hPV]
    noncomm_ring
  have hnorm : ‖P₀‖ ≤ 1 := norm_projection_le_one P₀ hP₀ hP₀star
  have hfirst : ‖(U - V) * P₀ * star U‖ ≤ ‖U - V‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU)]
    calc
      ‖(U - V) * P₀‖ ≤ ‖U - V‖ * ‖P₀‖ := norm_mul_le _ _
      _ ≤ ‖U - V‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖U - V‖ := mul_one _
  have hsecond : ‖V * P₀ * (star U - star V)‖ ≤ ‖U - V‖ := by
    rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ hV, ← star_sub]
    calc
      ‖P₀ * star (U - V)‖ ≤ ‖P₀‖ * ‖star (U - V)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖star (U - V)‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖U - V‖ := by rw [one_mul, norm_star]
  calc
    ‖U * P₀ * star U - P‖ ≤
        ‖(U - V) * P₀ * star U‖ + ‖V * P₀ * (star U - star V)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ ‖U - V‖ + ‖U - V‖ := add_le_add hfirst hsecond
    _ = 2 * ‖U - V‖ := by ring

end Adiabatic
