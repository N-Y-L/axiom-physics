import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic

/-!
# Estimates for chronological products

Time slicing approximates a nonautonomous evolution by successive frozen
Hamiltonians. The comparison estimate uses domain norms only on the right
and physical-space contractions on the left, as required for unbounded
generators. These finite-product lemmas do not assert convergence or
existence of a nonautonomous propagator.
-/

namespace Adiabatic.Unbounded

/-- Chronological multiplication, with the earliest factor acting first. -/
def timeOrderedProduct {A : Type*} [Monoid A] (a : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => a n * timeOrderedProduct a n

@[simp] theorem timeOrderedProduct_zero {A : Type*} [Monoid A] (a : ℕ → A) :
    timeOrderedProduct a 0 = 1 := rfl

@[simp] theorem timeOrderedProduct_succ {A : Type*} [Monoid A] (a : ℕ → A) (n : ℕ) :
    timeOrderedProduct a (n + 1) = a n * timeOrderedProduct a n := rfl

/-- A chronological product of unitary factors is unitary. -/
theorem timeOrderedProduct_mem_unitary {A : Type*} [Monoid A] [StarMul A]
    (a : ℕ → A) (ha : ∀ n, a n ∈ unitary A) (n : ℕ) :
    timeOrderedProduct a n ∈ unitary A := by
  induction n with
  | zero => exact (unitary A).one_mem
  | succ n ih => exact (unitary A).mul_mem (ha n) ih

/-- Products of small norm increases have an exponential bound. -/
theorem norm_timeOrderedProduct_le_exp_sum {A : Type*} [NormedRing A]
    [NormOneClass A] (a : ℕ → A) (ε : ℕ → ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1 + ε n) (n : ℕ) :
    ‖timeOrderedProduct a n‖ ≤ Real.exp (∑ k ∈ Finset.range n, ε k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖timeOrderedProduct a (n + 1)‖ ≤ ‖a n‖ * ‖timeOrderedProduct a n‖ := norm_mul_le _ _
      _ ≤ Real.exp (ε n) * Real.exp (∑ k ∈ Finset.range n, ε k) := by
        apply mul_le_mul ((ha n).trans (by simpa [add_comm] using Real.add_one_le_exp (ε n))) ih
          (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (∑ k ∈ Finset.range (n + 1), ε k) := by
        rw [← Real.exp_add, Finset.sum_range_succ, add_comm]

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Domain preservation passes to the chronological product. -/
theorem timeOrderedProduct_preserves_domain (j : D →L[ℂ] E)
    (a : ℕ → E →L[ℂ] E) (b : ℕ → D →L[ℂ] D)
    (hab : ∀ n x, a n (j x) = j (b n x)) (n : ℕ) (x : D) :
    timeOrderedProduct a n (j x) = j (timeOrderedProduct b n x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [timeOrderedProduct_succ, ContinuousLinearMap.mul_apply, ih] using
      (hab n (timeOrderedProduct b n x))

/-- A telescoping comparison for products acting on a common domain.
Each one-step error is measured from the domain norm to the physical norm. -/
theorem norm_timeOrderedProduct_sub_comp_le (j : D →L[ℂ] E)
    (a b : ℕ → E →L[ℂ] E) (bD : ℕ → D →L[ℂ] D)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hbD : ∀ n x, b n (j x) = j (bD n x)) (n : ℕ) :
    ‖(timeOrderedProduct a n - timeOrderedProduct b n).comp j‖ ≤
      ∑ k ∈ Finset.range n, ‖(a k - b k).comp j‖ * ‖timeOrderedProduct bD k‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (timeOrderedProduct a (n + 1) - timeOrderedProduct b (n + 1)).comp j =
        (a n).comp ((timeOrderedProduct a n - timeOrderedProduct b n).comp j) +
        ((a n - b n).comp j).comp (timeOrderedProduct bD n) := by
      ext x
      simp only [timeOrderedProduct_succ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.mul_apply, map_sub,
        ← timeOrderedProduct_preserves_domain j b bD hbD n x]
      abel
    rw [hsplit, Finset.sum_range_succ]
    calc
      _ ≤ ‖(a n).comp ((timeOrderedProduct a n - timeOrderedProduct b n).comp j)‖ +
          ‖((a n - b n).comp j).comp (timeOrderedProduct bD n)‖ := norm_add_le _ _
      _ ≤ ‖(timeOrderedProduct a n - timeOrderedProduct b n).comp j‖ +
          ‖(a n - b n).comp j‖ * ‖timeOrderedProduct bD n‖ := by
        apply add_le_add _ (ContinuousLinearMap.opNorm_comp_le _ _)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ _ := add_le_add ih le_rfl

end Adiabatic.Unbounded
