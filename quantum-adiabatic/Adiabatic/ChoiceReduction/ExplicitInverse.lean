import Adiabatic.ReducedResolvent

/-!
# Algebra with supplied inverse data

Two-sided inverses can be retained as data instead of selected from an
existence proof. Their uniqueness, the resolvent identity, and the reduced
commutator construction then require no choice. This module does not
construct inverse data from a spectral gap or prove analytic regularity.
-/

namespace Adiabatic.ChoiceReduction

/-- A specified inverse, together with its two inverse identities. -/
structure ExplicitInverse {A : Type*} [Monoid A] (a : A) where
  value : A
  left_inverse : value * a = 1
  right_inverse : a * value = 1

namespace ExplicitInverse

variable {A : Type*} [Monoid A] {a : A}

/-- A left inverse and a right inverse of the same element agree. -/
theorem left_right_unique {b c : A} (hb : b * a = 1) (hc : a * c = 1) : b = c := by
  calc
    b = b * (a * c) := by rw [hc, mul_one]
    _ = (b * a) * c := (mul_assoc _ _ _).symm
    _ = c := by rw [hb, one_mul]

/-- Specified two-sided inverses have the same value. -/
theorem value_unique (r s : ExplicitInverse a) : r.value = s.value :=
  left_right_unique r.left_inverse s.right_inverse

/-- An inverse supplied as data determines a unit without a choice operation. -/
def toUnit (r : ExplicitInverse a) : Aˣ where
  val := a
  inv := r.value
  val_inv := r.right_inverse
  inv_val := r.left_inverse

/-- Unit data supply an explicit inverse. -/
def ofUnit (u : Aˣ) : ExplicitInverse (u : A) where
  value := ↑(u⁻¹)
  left_inverse := u.inv_val
  right_inverse := u.val_inv

/-- Inverse existence implies unique existence as a proposition. -/
theorem exists_unique_of_exists
    (h : ∃ b : A, b * a = 1 ∧ a * b = 1) :
    ∃! b : A, b * a = 1 ∧ a * b = 1 := by
  obtain ⟨b, hb, hb'⟩ := h
  refine ⟨b, ⟨hb, hb'⟩, ?_⟩
  intro c hc
  exact left_right_unique hc.1 hb'

end ExplicitInverse

section Ring

variable {A : Type*} [Ring A]

/-- Difference of specified inverses in a possibly noncommutative ring. -/
theorem inverse_difference {a b : A} (r : ExplicitInverse a) (s : ExplicitInverse b) :
    r.value - s.value = r.value * (b - a) * s.value := by
  rw [mul_sub, sub_mul, mul_assoc, s.right_inverse, mul_one,
    r.left_inverse, one_mul]

/-- The reduced commutator obtained from inverse data for the augmented operator. -/
def commutatorFromInverse (H P dP : A) (r : ExplicitInverse (H + P)) : A :=
  reducedCommutator (reducedResolvent r.value P) P dP

/-- Inverse data and the spectral-block identities solve the Kato commutator equation. -/
theorem commutatorFromInverse_equation {H P dP : A}
    (r : ExplicitInverse (H + P))
    (hP : P * P = P) (hHP : H * P = 0) (hPH : P * H = 0) :
    H * commutatorFromInverse H P dP r - commutatorFromInverse H P dP r * H =
      katoGenerator P dP :=
  reducedResolvent_commutator hP hHP hPH r.left_inverse r.right_inverse

end Ring

/-- Specified inverse data for a linear map between different spaces. -/
structure ExplicitLinearInverse {R D E : Type*} [Semiring R]
    [AddCommMonoid D] [AddCommMonoid E] [Module R D] [Module R E]
    (A : D →ₗ[R] E) where
  inverse : E →ₗ[R] D
  left_inverse : inverse.comp A = LinearMap.id
  right_inverse : A.comp inverse = LinearMap.id

namespace ExplicitLinearInverse

variable {R D E : Type*} [Semiring R]
  [AddCommMonoid D] [AddCommMonoid E] [Module R D] [Module R E]
  {A : D →ₗ[R] E}

/-- The supplied inverse cancels its domain map. -/
theorem inverse_apply (r : ExplicitLinearInverse A) (x : D) :
    r.inverse (A x) = x :=
  congrArg (fun f : D →ₗ[R] D => f x) r.left_inverse

/-- The domain map cancels its supplied inverse. -/
theorem apply_inverse (r : ExplicitLinearInverse A) (x : E) :
    A (r.inverse x) = x :=
  congrArg (fun f : E →ₗ[R] E => f x) r.right_inverse

/-- Explicit inverses of a linear map are pointwise unique. -/
theorem pointwise_unique (r s : ExplicitLinearInverse A) (x : E) :
    r.inverse x = s.inverse x := by
  calc
    r.inverse x = r.inverse (A (s.inverse x)) := congrArg r.inverse (s.apply_inverse x).symm
    _ = s.inverse x := r.inverse_apply (s.inverse x)

end ExplicitLinearInverse

section LinearResolvent

variable {R D E : Type*} [Ring R]
  [AddCommGroup D] [AddCommGroup E] [Module R D] [Module R E]

/-- A linear map preserves subtraction by cancellation in the additive group. -/
theorem linear_map_sub (f : D →ₗ[R] E) (x y : D) : f (x - y) = f x - f y := by
  apply eq_sub_iff_add_eq.mpr
  calc
    f (x - y) + f y = f ((x - y) + y) := (f.map_add _ _).symm
    _ = f x := congrArg f (sub_add_cancel x y)

/-- The inverse-difference identity for maps from a common domain to a physical space. -/
theorem linear_inverse_difference {A B : D →ₗ[R] E}
    (r : ExplicitLinearInverse A) (s : ExplicitLinearInverse B) :
    r.inverse - s.inverse = (r.inverse.comp (B - A)).comp s.inverse := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, linear_map_sub]
  rw [s.apply_inverse, r.inverse_apply]

end LinearResolvent

section ResolventPencil

variable {R D E : Type*} [CommRing R]
  [AddCommGroup D] [AddCommGroup E] [Module R D] [Module R E]

/-- The first resolvent identity for explicit inverses of the pencil `H - z j`.
The inverse maps from the physical space into the common domain. -/
theorem linear_resolvent_identity (H j : D →ₗ[R] E) (z w : R)
    (r : ExplicitLinearInverse (H - z • j))
    (s : ExplicitLinearInverse (H - w • j)) :
    r.inverse - s.inverse = (z - w) • ((r.inverse.comp j).comp s.inverse) := by
  rw [linear_inverse_difference]
  have hp : (H - w • j) - (H - z • j) = (z - w) • j := by
    rw [sub_sub_sub_cancel_left, sub_smul]
  rw [hp]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

end ResolventPencil

end Adiabatic.ChoiceReduction
