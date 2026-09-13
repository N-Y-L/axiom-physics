import Adiabatic.Projection

/-!
# Algebraic reduced resolvent

For an isolated eigenvalue `e`, the shifted Hamiltonian is `H - e • 1`.
If this shift annihilates a projection `P`, an inverse of its sum with `P`
produces a reduced resolvent. The theorems here prove the resulting algebraic
commutator equation. They do not assert that a spectral gap supplies the
inverse, or prove differentiability of the resulting path.
-/

namespace Adiabatic

variable {A : Type*} [Ring A]

/-- Remove the projection block from the inverse of the augmented Hamiltonian. -/
def reducedResolvent (Ainv P : A) : A := Ainv - P

/-- The inverse of the augmented Hamiltonian acts identically on the projection. -/
theorem augmentedInverse_mul_projection {H P Ainv : A}
    (hP : P * P = P) (hHP : H * P = 0)
    (hleft : Ainv * (H + P) = 1) : Ainv * P = P := by
  calc
    Ainv * P = Ainv * ((H + P) * P) := by rw [add_mul, hHP, hP, zero_add]
    _ = (Ainv * (H + P)) * P := (mul_assoc _ _ _).symm
    _ = P := by rw [hleft, one_mul]

/-- The projection also acts identically on the corresponding inverse block. -/
theorem projection_mul_augmentedInverse {H P Ainv : A}
    (hP : P * P = P) (hPH : P * H = 0)
    (hright : (H + P) * Ainv = 1) : P * Ainv = P := by
  calc
    P * Ainv = (P * (H + P)) * Ainv := by rw [mul_add, hPH, hP, zero_add]
    _ = P * ((H + P) * Ainv) := mul_assoc _ _ _
    _ = P := by rw [hright, mul_one]

/-- The reduced resolvent annihilates the selected eigenspace. -/
theorem reducedResolvent_mul_projection {H P Ainv : A}
    (hP : P * P = P) (hHP : H * P = 0)
    (hleft : Ainv * (H + P) = 1) : reducedResolvent Ainv P * P = 0 := by
  simp only [reducedResolvent, sub_mul,
    augmentedInverse_mul_projection hP hHP hleft, hP, sub_self]

/-- The range of the reduced resolvent has no projection component. -/
theorem projection_mul_reducedResolvent {H P Ainv : A}
    (hP : P * P = P) (hPH : P * H = 0)
    (hright : (H + P) * Ainv = 1) : P * reducedResolvent Ainv P = 0 := by
  simp only [reducedResolvent, mul_sub,
    projection_mul_augmentedInverse hP hPH hright, hP, sub_self]

/-- The shifted Hamiltonian times the reduced resolvent is the complement. -/
theorem mul_reducedResolvent {H P Ainv : A}
    (hP : P * P = P) (hHP : H * P = 0) (hPH : P * H = 0)
    (hright : (H + P) * Ainv = 1) : H * reducedResolvent Ainv P = 1 - P := by
  have hPA := projection_mul_augmentedInverse hP hPH hright
  simp only [reducedResolvent, mul_sub, hHP, sub_zero]
  apply eq_sub_iff_add_eq.mpr
  calc
    H * Ainv + P = (H + P) * Ainv := by rw [add_mul, hPA]
    _ = 1 := hright

/-- The reduced resolvent times the shifted Hamiltonian is the complement. -/
theorem reducedResolvent_mul {H P Ainv : A}
    (hP : P * P = P) (hHP : H * P = 0) (hPH : P * H = 0)
    (hleft : Ainv * (H + P) = 1) : reducedResolvent Ainv P * H = 1 - P := by
  have hAP := augmentedInverse_mul_projection hP hHP hleft
  simp only [reducedResolvent, sub_mul, hPH, sub_zero]
  apply eq_sub_iff_add_eq.mpr
  calc
    Ainv * H + P = Ainv * (H + P) := by rw [mul_add, hAP]
    _ = 1 := hleft

/-- A candidate commutator solution built from a reduced resolvent. -/
def reducedCommutator (R P dP : A) : A := R * dP * P + P * dP * R

/-- Reduced resolvent identities imply the Kato commutator equation.
The algebraic identity does not itself require a derivative hypothesis on `dP`. -/
theorem reducedCommutator_commutator {H R P dP : A}
    (hHP : H * P = 0) (hPH : P * H = 0)
    (hHR : H * R = 1 - P) (hRH : R * H = 1 - P) :
    H * reducedCommutator R P dP - reducedCommutator R P dP * H =
      katoGenerator P dP := by
  calc
    H * reducedCommutator R P dP - reducedCommutator R P dP * H =
        (H * R) * dP * P + (H * P) * dP * R -
          (R * dP) * (P * H) - (P * dP) * (R * H) := by
      unfold reducedCommutator
      noncomm_ring
    _ = katoGenerator P dP := by
      rw [hHR, hHP, hPH, hRH]
      unfold katoGenerator
      noncomm_ring

/-- An augmented inverse supplies the algebraic commutator solution. -/
theorem reducedResolvent_commutator {H P dP Ainv : A}
    (hP : P * P = P) (hHP : H * P = 0) (hPH : P * H = 0)
    (hleft : Ainv * (H + P) = 1) (hright : (H + P) * Ainv = 1) :
    H * reducedCommutator (reducedResolvent Ainv P) P dP -
        reducedCommutator (reducedResolvent Ainv P) P dP * H =
      katoGenerator P dP :=
  reducedCommutator_commutator hHP hPH
    (mul_reducedResolvent hP hHP hPH hright)
    (reducedResolvent_mul hP hHP hPH hleft)

section Star

variable [StarRing A]

/-- The commutator solution is self-adjoint for self-adjoint data. -/
theorem star_reducedCommutator {R P dP : A}
    (hR : star R = R) (hP : star P = P) (hdP : star dP = dP) :
    star (reducedCommutator R P dP) = reducedCommutator R P dP := by
  simp only [reducedCommutator, star_add, star_mul, hR, hP, hdP]
  noncomm_ring

end Star

end Adiabatic
