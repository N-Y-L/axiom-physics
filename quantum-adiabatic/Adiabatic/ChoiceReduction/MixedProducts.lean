import Adiabatic.ChoiceReduction.FiniteProducts
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Finite product comparison with separate physical and domain bounds

Let `A` act on the physical space, `B` on the common domain, and `M` represent
maps from the domain to the physical space. The commuting left and right
actions on `M` model composition. A fixed `j : M` represents the inclusion.

The product defect `Aprod j - j Bprod` is controlled by the local defects
`aₖ j - j bₖ`, weighted by the sizes of domain prefixes. Only the physical
factors must be contractions. All actions, sizes, and order laws are explicit
data; no operator norm, inclusion, or propagator is constructed here.
-/

namespace Adiabatic.ChoiceReduction

/-- Commuting unital multiplicative actions, additive in the cross-space variable. -/
structure MixedAction (A B M : Type*) [Monoid A] [Monoid B] [AddCommGroup M] where
  left : A → M → M
  right : M → B → M
  left_one : ∀ x, left 1 x = x
  right_one : ∀ x, right x 1 = x
  left_mul : ∀ a b x, left (a * b) x = left a (left b x)
  right_mul : ∀ x a b, right x (a * b) = right (right x a) b
  left_right : ∀ a x b, left a (right x b) = right (left a x) b
  left_add : ∀ a x y, left a (x + y) = left a x + left a y
  right_add : ∀ x y b, right (x + y) b = right x b + right y b

namespace MixedAction

variable {A B M : Type*} [Monoid A] [Monoid B] [AddCommGroup M]
variable (act : MixedAction A B M)

/-- The physical action preserves subtraction. -/
theorem left_sub (a : A) (x y : M) : act.left a (x - y) = act.left a x - act.left a y := by
  apply eq_sub_iff_add_eq.mpr
  calc
    act.left a (x - y) + act.left a y = act.left a ((x - y) + y) :=
      (act.left_add _ _ _).symm
    _ = act.left a x := congrArg (act.left a) (sub_add_cancel x y)

/-- The domain action preserves subtraction. -/
theorem right_sub (x y : M) (b : B) : act.right (x - y) b = act.right x b - act.right y b := by
  apply eq_sub_iff_add_eq.mpr
  calc
    act.right (x - y) b + act.right y b = act.right ((x - y) + y) b :=
      (act.right_add _ _ _).symm
    _ = act.right x b := congrArg (fun m => act.right m b) (sub_add_cancel x y)

end MixedAction

section Defects

variable {A B M : Type*} [Monoid A] [Monoid B] [AddCommGroup M]
variable (act : MixedAction A B M)

/-- The defect of a single physical/domain factor pair relative to `j`. -/
def localMixedDefect (j : M) (a : A) (b : B) : M := act.left a j - act.right j b

/-- The defect of the chronological products relative to `j`. -/
def mixedProductError (j : M) (a : ℕ → A) (b : ℕ → B) (n : ℕ) : M :=
  act.left (chronologicalProduct a n) j - act.right j (chronologicalProduct b n)

/-- The empty products have zero defect. -/
theorem mixedProductError_zero (j : M) (a : ℕ → A) (b : ℕ → B) :
    mixedProductError act j a b 0 = 0 := by
  change act.left 1 j - act.right j 1 = 0
  rw [act.left_one, act.right_one, sub_self]

/-- The next product defect is the propagated previous defect plus the local
mixed defect acting on the domain prefix. -/
theorem mixedProductError_succ (j : M) (a : ℕ → A) (b : ℕ → B) (n : ℕ) :
    mixedProductError act j a b (n + 1) =
      act.left (a n) (mixedProductError act j a b n) +
        act.right (localMixedDefect act j (a n) (b n)) (chronologicalProduct b n) := by
  change act.left (a n * chronologicalProduct a n) j -
      act.right j (b n * chronologicalProduct b n) =
    act.left (a n) (act.left (chronologicalProduct a n) j -
      act.right j (chronologicalProduct b n)) +
    act.right (act.left (a n) j - act.right j (b n)) (chronologicalProduct b n)
  rw [act.left_mul, act.right_mul, act.left_sub, act.right_sub, act.left_right,
    sub_add_sub_cancel]

end Defects

/-- A cross-space size bounded under physical and domain composition. -/
structure MixedSize {A B M R : Type*} [Ring A] [Ring B] [AddCommGroup M]
    [Semiring R] [PartialOrder R] (act : MixedAction A B M)
    (physical : SubmultiplicativeSize A R) (domain : SubmultiplicativeSize B R) where
  size : M → R
  nonneg : ∀ x, 0 ≤ size x
  zero : size 0 = 0
  add : ∀ x y, size (x + y) ≤ size x + size y
  left : ∀ a x, size (act.left a x) ≤ physical.size a * size x
  right : ∀ x b, size (act.right x b) ≤ size x * domain.size b

section Bounds

variable {A B M R : Type*} [Ring A] [Ring B] [AddCommGroup M]
  [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {act : MixedAction A B M}
  {physical : SubmultiplicativeSize A R} {domain : SubmultiplicativeSize B R}
variable (s : MixedSize act physical domain)

/-- Physical contractions give a product-error bound weighted by domain prefix
sizes. The domain factors need not be contractions. -/
theorem mixedProductError_le (j : M) (a : ℕ → A) (b : ℕ → B) (n : ℕ)
    (ha : ∀ k < n, physical.size (a k) ≤ 1) :
    s.size (mixedProductError act j a b n) ≤
      initialSum (fun k => s.size (localMixedDefect act j (a k) (b k)) *
        domain.size (chronologicalProduct b k)) n := by
  induction n with
  | zero =>
      rw [mixedProductError_zero, s.zero]
      exact le_refl 0
  | succ n ih =>
      change s.size (mixedProductError act j a b (n + 1)) ≤
        s.size (localMixedDefect act j (a n) (b n)) *
          domain.size (chronologicalProduct b n) +
        initialSum (fun k => s.size (localMixedDefect act j (a k) (b k)) *
          domain.size (chronologicalProduct b k)) n
      rw [mixedProductError_succ]
      calc
        _ ≤ s.size (act.left (a n) (mixedProductError act j a b n)) +
            s.size (act.right (localMixedDefect act j (a n) (b n))
              (chronologicalProduct b n)) := s.add _ _
        _ ≤ physical.size (a n) * s.size (mixedProductError act j a b n) +
            s.size (act.right (localMixedDefect act j (a n) (b n))
              (chronologicalProduct b n)) :=
          IsOrderedAddMonoid.add_le_add_left _ _ (s.left _ _) _
        _ ≤ 1 * s.size (mixedProductError act j a b n) +
            s.size (act.right (localMixedDefect act j (a n) (b n))
              (chronologicalProduct b n)) :=
          IsOrderedAddMonoid.add_le_add_left _ _
            (mul_le_mul_of_nonneg_right (ha n (Nat.lt_succ_self n)) (s.nonneg _)) _
        _ = s.size (mixedProductError act j a b n) +
            s.size (act.right (localMixedDefect act j (a n) (b n))
              (chronologicalProduct b n)) := by rw [one_mul]
        _ ≤ initialSum (fun k => s.size (localMixedDefect act j (a k) (b k)) *
              domain.size (chronologicalProduct b k)) n +
            s.size (act.right (localMixedDefect act j (a n) (b n))
              (chronologicalProduct b n)) :=
          IsOrderedAddMonoid.add_le_add_left _ _
            (ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))) _
        _ ≤ initialSum (fun k => s.size (localMixedDefect act j (a k) (b k)) *
              domain.size (chronologicalProduct b k)) n +
            s.size (localMixedDefect act j (a n) (b n)) *
              domain.size (chronologicalProduct b n) :=
          IsOrderedAddMonoid.add_le_add_right _ _ (s.right _ _) _
        _ = _ := add_comm _ _

/-- Local-defect bounds and domain-prefix bounds give an explicit weighted sum. -/
theorem mixedProductError_le_bounds (j : M) (a : ℕ → A) (b : ℕ → B)
    (ε γ : ℕ → R) (n : ℕ) (ha : ∀ k < n, physical.size (a k) ≤ 1)
    (hε : ∀ k < n, s.size (localMixedDefect act j (a k) (b k)) ≤ ε k)
    (hγ : ∀ k < n, domain.size (chronologicalProduct b k) ≤ γ k) :
    s.size (mixedProductError act j a b n) ≤ initialSum (fun k => ε k * γ k) n := by
  refine (mixedProductError_le s j a b n ha).trans (initialSum_le _ _ n ?_)
  intro k hk
  exact mul_le_mul (hε k hk) (hγ k hk) (domain.nonneg _)
    ((s.nonneg _).trans (hε k hk))

/-- Bounds on each domain factor multiply to bound its chronological prefix. -/
theorem domainPrefix_size_le (b : ℕ → B) (β : ℕ → R) (n : ℕ)
    (hb : ∀ k < n, domain.size (b k) ≤ β k) :
    domain.size (chronologicalProduct b n) ≤ chronologicalProduct β n := by
  induction n with
  | zero => exact domain.one
  | succ n ih =>
      change domain.size (b n * chronologicalProduct b n) ≤
        β n * chronologicalProduct β n
      exact (domain.mul _ _).trans (mul_le_mul (hb n (Nat.lt_succ_self n))
        (ih (fun k hk => hb k (Nat.lt_succ_of_lt hk))) (domain.nonneg _)
        ((domain.nonneg _).trans (hb n (Nat.lt_succ_self n))))

/-- Local physical contraction, local defect, and local domain growth bounds
control the full product error. The weights are products of domain bounds. -/
theorem mixedProductError_le_local_bounds (j : M) (a : ℕ → A) (b : ℕ → B)
    (ε β : ℕ → R) (n : ℕ) (ha : ∀ k < n, physical.size (a k) ≤ 1)
    (hε : ∀ k < n, s.size (localMixedDefect act j (a k) (b k)) ≤ ε k)
    (hb : ∀ k < n, domain.size (b k) ≤ β k) :
    s.size (mixedProductError act j a b n) ≤
      initialSum (fun k => ε k * chronologicalProduct β k) n := by
  apply mixedProductError_le_bounds s j a b ε (chronologicalProduct β) n ha hε
  intro k hk
  exact domainPrefix_size_le b β k (fun l hl => hb l (Nat.lt_trans hl hk))

/-- Uniform local defects and a uniform domain-prefix bound give an `n ε K` error. -/
theorem mixedProductError_le_uniform (j : M) (a : ℕ → A) (b : ℕ → B)
    (ε K : R) (n : ℕ) (ha : ∀ k < n, physical.size (a k) ≤ 1)
    (hε : ∀ k < n, s.size (localMixedDefect act j (a k) (b k)) ≤ ε)
    (hK : ∀ k < n, domain.size (chronologicalProduct b k) ≤ K) :
    s.size (mixedProductError act j a b n) ≤ (n : R) * (ε * K) :=
  (mixedProductError_le_bounds s j a b (fun _ => ε) (fun _ => K) n ha hε hK).trans_eq
    (initialSum_const (ε * K) n)

end Bounds

section LinearMaps

variable {K D E : Type*} [Semiring K]
  [AddCommGroup D] [AddCommGroup E] [Module K D] [Module K E]

/-- Physical endomorphisms act by composition on the left, domain
endomorphisms by composition on the right. -/
def linearMapMixedAction :
    MixedAction (E →ₗ[K] E) (D →ₗ[K] D) (D →ₗ[K] E) where
  left a x := a.comp x
  right x b := x.comp b
  left_one _ := LinearMap.ext fun _ => rfl
  right_one _ := LinearMap.ext fun _ => rfl
  left_mul _ _ _ := LinearMap.ext fun _ => rfl
  right_mul _ _ _ := LinearMap.ext fun _ => rfl
  left_right _ _ _ := LinearMap.ext fun _ => rfl
  left_add a x y := LinearMap.ext fun d => a.map_add (x d) (y d)
  right_add _ _ _ := LinearMap.ext fun _ => rfl

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {physical : SubmultiplicativeSize (E →ₗ[K] E) R}
  {domain : SubmultiplicativeSize (D →ₗ[K] D) R}

/-- The mixed comparison for linear maps between a domain and physical space,
with all global errors derived from local defect and domain growth bounds. -/
theorem linearMap_mixedProduct_error_le
    (s : MixedSize linearMapMixedAction physical domain)
    (j : D →ₗ[K] E) (a : ℕ → E →ₗ[K] E) (b : ℕ → D →ₗ[K] D)
    (ε β : ℕ → R) (n : ℕ) (ha : ∀ k < n, physical.size (a k) ≤ 1)
    (hε : ∀ k < n, s.size ((a k).comp j - j.comp (b k)) ≤ ε k)
    (hb : ∀ k < n, domain.size (b k) ≤ β k) :
    s.size ((chronologicalProduct a n).comp j - j.comp (chronologicalProduct b n)) ≤
      initialSum (fun k => ε k * chronologicalProduct β k) n :=
  mixedProductError_le_local_bounds s j a b ε β n ha hε hb

end LinearMaps

end Adiabatic.ChoiceReduction
