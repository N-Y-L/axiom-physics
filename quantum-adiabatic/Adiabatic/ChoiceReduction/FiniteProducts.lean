import Mathlib.Algebra.Order.Ring.Defs

/-!
# Constructive stability of finite chronological products

The difference of two products satisfies a discrete variation-of-constants
identity. If all factors are contractions, its size is bounded by the sum of
the local errors. The scalar order and submultiplicative size are supplied as
explicit algebraic data; this file does not construct a real operator norm.
-/

namespace Adiabatic.ChoiceReduction

/-- Chronological multiplication: the latest factor acts on the left. -/
def chronologicalProduct {A : Type*} [Monoid A] (a : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => a n * chronologicalProduct a n

/-- A finite sum defined by recursion, without selecting an enumeration. -/
def initialSum {R : Type*} [AddMonoid R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => f n + initialSum f n

/-- The solution of a discrete inhomogeneous linear evolution with zero initial
value. Its input `e n` is added after step `n`. -/
def forcedEvolution {A : Type*} [Ring A] (a e : ℕ → A) : ℕ → A
  | 0 => 0
  | n + 1 => a n * forcedEvolution a e n + e n

/-- The product error obeys the discrete variation-of-constants identity. -/
theorem chronologicalProduct_sub {A : Type*} [Ring A] (a b : ℕ → A) (n : ℕ) :
    chronologicalProduct a n - chronologicalProduct b n =
      forcedEvolution a (fun k => (a k - b k) * chronologicalProduct b k) n := by
  induction n with
  | zero => exact sub_self 1
  | succ n ih =>
    change a n * chronologicalProduct a n - b n * chronologicalProduct b n =
      a n * forcedEvolution a (fun k => (a k - b k) * chronologicalProduct b k) n +
        (a n - b n) * chronologicalProduct b n
    rw [← ih, mul_sub, sub_mul, sub_add_sub_cancel]

/-- The laws of a submultiplicative size with values in an ordered semiring.
No definiteness or completeness is needed for the finite-product estimates. -/
structure SubmultiplicativeSize (A R : Type*) [Ring A] [Semiring R] [PartialOrder R] where
  size : A → R
  nonneg : ∀ a, 0 ≤ size a
  zero : size 0 = 0
  one : size 1 ≤ 1
  add : ∀ a b, size (a + b) ≤ size a + size b
  mul : ∀ a b, size (a * b) ≤ size a * size b

section Bounds

variable {A R : Type*} [Ring A] [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable (s : SubmultiplicativeSize A R)

/-- Products of contractions remain contractions. -/
theorem chronologicalProduct_size_le_one (a : ℕ → A) (n : ℕ)
    (ha : ∀ k < n, s.size (a k) ≤ 1) : s.size (chronologicalProduct a n) ≤ 1 := by
  induction n with
  | zero => exact s.one
  | succ n ih =>
    change s.size (a n * chronologicalProduct a n) ≤ 1
    calc
      s.size (a n * chronologicalProduct a n) ≤
          s.size (a n) * s.size (chronologicalProduct a n) := s.mul _ _
      _ ≤ 1 * 1 := mul_le_mul (ha n (Nat.lt_succ_self n))
        (ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))) (s.nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- Contractive propagation accumulates at most the sum of the forcing sizes. -/
theorem forcedEvolution_size_le (a e : ℕ → A) (n : ℕ)
    (ha : ∀ k < n, s.size (a k) ≤ 1) :
    s.size (forcedEvolution a e n) ≤ initialSum (fun k => s.size (e k)) n := by
  induction n with
  | zero => exact le_of_eq s.zero
  | succ n ih =>
    change s.size (a n * forcedEvolution a e n + e n) ≤
      s.size (e n) + initialSum (fun k => s.size (e k)) n
    calc
      s.size (a n * forcedEvolution a e n + e n) ≤
          s.size (a n * forcedEvolution a e n) + s.size (e n) := s.add _ _
      _ ≤ s.size (a n) * s.size (forcedEvolution a e n) + s.size (e n) :=
        IsOrderedAddMonoid.add_le_add_left _ _ (s.mul _ _) _
      _ ≤ 1 * s.size (forcedEvolution a e n) + s.size (e n) :=
        IsOrderedAddMonoid.add_le_add_left _ _ (mul_le_mul_of_nonneg_right
          (ha n (Nat.lt_succ_self n)) (s.nonneg _)) _
      _ = s.size (forcedEvolution a e n) + s.size (e n) := by rw [one_mul]
      _ ≤ initialSum (fun k => s.size (e k)) n + s.size (e n) :=
        IsOrderedAddMonoid.add_le_add_left _ _
          (ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))) _
      _ = s.size (e n) + initialSum (fun k => s.size (e k)) n := add_comm _ _

/-- Finite sums respect pointwise upper bounds. -/
theorem initialSum_le (f g : ℕ → R) (n : ℕ) (h : ∀ k < n, f k ≤ g k) :
    initialSum f n ≤ initialSum g n := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    exact (IsOrderedAddMonoid.add_le_add_left _ _ (h n (Nat.lt_succ_self n)) _).trans
      (IsOrderedAddMonoid.add_le_add_right _ _
        (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) _)

/-- For contractive factors, the error of the chronological products is at most
the sum of the factor errors. This is the finite time-slicing stability estimate. -/
theorem chronologicalProduct_error_le (a b : ℕ → A) (n : ℕ)
    (ha : ∀ k < n, s.size (a k) ≤ 1) (hb : ∀ k < n, s.size (b k) ≤ 1) :
    s.size (chronologicalProduct a n - chronologicalProduct b n) ≤
      initialSum (fun k => s.size (a k - b k)) n := by
  rw [chronologicalProduct_sub]
  refine (forcedEvolution_size_le s a _ n ha).trans (initialSum_le _ _ n ?_)
  intro k hk
  calc
    s.size ((a k - b k) * chronologicalProduct b k) ≤
        s.size (a k - b k) * s.size (chronologicalProduct b k) := s.mul _ _
    _ ≤ s.size (a k - b k) * 1 :=
      mul_le_mul_of_nonneg_left
        (chronologicalProduct_size_le_one s b k (fun j hj => hb j (Nat.lt_trans hj hk)))
        (s.nonneg _)
    _ = s.size (a k - b k) := mul_one _

/-- Any supplied local-error bounds may replace the exact factor sizes. -/
theorem chronologicalProduct_error_le_sum (a b : ℕ → A) (ε : ℕ → R) (n : ℕ)
    (ha : ∀ k < n, s.size (a k) ≤ 1) (hb : ∀ k < n, s.size (b k) ≤ 1)
    (hε : ∀ k < n, s.size (a k - b k) ≤ ε k) :
    s.size (chronologicalProduct a n - chronologicalProduct b n) ≤ initialSum ε n :=
  (chronologicalProduct_error_le s a b n ha hb).trans (initialSum_le _ _ n hε)

omit [PartialOrder R] [IsOrderedRing R] in
/-- A constant finite sum is multiplication by its number of terms. -/
theorem initialSum_const (c : R) (n : ℕ) : initialSum (fun _ => c) n = (n : R) * c := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul]; rfl
  | succ n ih =>
    change c + initialSum (fun _ => c) n = (↑(n + 1) : R) * c
    rw [ih, Nat.cast_succ, add_mul, one_mul, add_comm]

/-- A uniform one-step error `ε` gives an `n ε` product error. -/
theorem chronologicalProduct_error_le_mul (a b : ℕ → A) (ε : R) (n : ℕ)
    (ha : ∀ k < n, s.size (a k) ≤ 1) (hb : ∀ k < n, s.size (b k) ≤ 1)
    (hε : ∀ k < n, s.size (a k - b k) ≤ ε) :
    s.size (chronologicalProduct a n - chronologicalProduct b n) ≤ (n : R) * ε := by
  exact (chronologicalProduct_error_le_sum s a b (fun _ => ε) n ha hb hε).trans_eq
    (initialSum_const ε n)

end Bounds

end Adiabatic.ChoiceReduction
