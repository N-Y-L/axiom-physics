import Adiabatic.ChoiceReduction.ExplicitInverse
import Mathlib.Algebra.Order.Ring.Defs

/-!
# An inverse extracted from a lift of the coordinate swap

For an injective linear map `S : X → Y`, set `j(y, x) = (y, S x)`.
A linear lift `L` satisfying `j L = swap j` determines the inverse of `S`:
it is the second coordinate of `L(y, 0)`. A bound on `L`, together with
product-size bounds, gives the corresponding inverse bound.

This is the algebraic step in the bounded-lift obstruction. It does not
prove evolution uniqueness or formalize a set-theoretic countermodel.
-/

namespace Adiabatic.ChoiceReduction

namespace LiftObstruction

variable {K X Y : Type*} [Semiring K]
  [AddCommMonoid X] [AddCommMonoid Y] [Module K X] [Module K Y]

/-- The domain inclusion used in the coordinate-swap reduction. -/
def embedding (S : X →ₗ[K] Y) : Y × X →ₗ[K] Y × Y :=
  (LinearMap.id : Y →ₗ[K] Y).prodMap S

/-- Interchange the two physical coordinates. -/
def swap : Y × Y →ₗ[K] Y × Y := (LinearEquiv.prodComm K Y Y).toLinearMap

/-- Extract a candidate inverse from the second coordinate of a supplied lift. -/
def inverseFromLift (L : Y × X →ₗ[K] Y × X) : Y →ₗ[K] X :=
  (LinearMap.snd K Y X).comp (L.comp (LinearMap.inl K Y X))

/-- Lifting the swap makes the extracted map a right inverse. No prior
surjectivity assumption on `S` is needed. -/
theorem right_inverse (S : X →ₗ[K] Y) (L : Y × X →ₗ[K] Y × X)
    (hL : (embedding S).comp L = (swap (K := K) (Y := Y)).comp (embedding S))
    (y : Y) : S (inverseFromLift L y) = y :=
  congrArg (fun f : Y × X →ₗ[K] Y × Y => (f (y, 0)).2) hL

/-- Injectivity gives the other inverse identity. -/
theorem left_inverse (S : X →ₗ[K] Y) (L : Y × X →ₗ[K] Y × X)
    (injective : Function.Injective S)
    (hL : (embedding S).comp L = (swap (K := K) (Y := Y)).comp (embedding S))
    (x : X) : inverseFromLift L (S x) = x :=
  injective (right_inverse S L hL (S x))

/-- A supplied lift of the swap constructs both inverse identities. -/
def explicitInverse (S : X →ₗ[K] Y) (L : Y × X →ₗ[K] Y × X)
    (injective : Function.Injective S)
    (hL : (embedding S).comp L = (swap (K := K) (Y := Y)).comp (embedding S)) :
    ExplicitLinearInverse S where
  inverse := inverseFromLift L
  left_inverse := LinearMap.ext (left_inverse S L injective hL)
  right_inverse := LinearMap.ext (right_inverse S L hL)

/-- Any compatible bound for the product-space lift bounds the extracted inverse.
The hypotheses bound the given lift and the two coordinate maps, not an inverse. -/
theorem inverse_size_le {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (L : Y × X →ₗ[K] Y × X) (sizeX : X → R) (sizeY : Y → R)
    (sizeD : Y × X → R) (C : R) (hC : 0 ≤ C)
    (projection_bound : ∀ p, sizeX p.2 ≤ sizeD p)
    (inclusion_bound : ∀ y, sizeD (y, 0) ≤ sizeY y)
    (lift_bound : ∀ p, sizeD (L p) ≤ C * sizeD p) (y : Y) :
    sizeX (inverseFromLift L y) ≤ C * sizeY y :=
  (projection_bound (L (y, 0))).trans ((lift_bound (y, 0)).trans
    (mul_le_mul_of_nonneg_left (inclusion_bound y) hC))

/-- A bounded swap lift of an injective map gives an explicitly bounded inverse. -/
theorem exists_bounded_inverse {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (S : X →ₗ[K] Y) (L : Y × X →ₗ[K] Y × X)
    (injective : Function.Injective S)
    (hL : (embedding S).comp L = (swap (K := K) (Y := Y)).comp (embedding S))
    (sizeX : X → R) (sizeY : Y → R) (sizeD : Y × X → R)
    (C : R) (hC : 0 ≤ C)
    (projection_bound : ∀ p, sizeX p.2 ≤ sizeD p)
    (inclusion_bound : ∀ y, sizeD (y, 0) ≤ sizeY y)
    (lift_bound : ∀ p, sizeD (L p) ≤ C * sizeD p) :
    ∃ inverse : Y →ₗ[K] X,
      (∀ x, inverse (S x) = x) ∧ (∀ y, S (inverse y) = y) ∧
        ∀ y, sizeX (inverse y) ≤ C * sizeY y :=
  ⟨inverseFromLift L, left_inverse S L injective hL, right_inverse S L hL,
    inverse_size_le L sizeX sizeY sizeD C hC projection_bound inclusion_bound lift_bound⟩

end LiftObstruction

end Adiabatic.ChoiceReduction
