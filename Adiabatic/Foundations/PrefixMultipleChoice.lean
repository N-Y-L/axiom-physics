import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite choices from an unbounded family of finite prefixes

For a family `A : ℕ → Type*`, a prefix of length `n + 1` specifies an
element of `A k` for each `k ≤ n`. Finite nonempty sets of prefixes at an
unbounded set of indices produce finite nonempty subsets of every `A k`.
The selected index for coordinate `k` is the least eligible natural number.
The proof does not select an element from each `A k` or enumerate the finite
sets of prefixes.
-/

namespace Adiabatic.Foundations

universe u

/-- A choice from each of the first `n + 1` members of a family. -/
def ChoicePrefix (A : ℕ → Type u) (n : ℕ) : Type u :=
  (k : Fin (n + 1)) → A k.val

/-- Evaluation of an unordered finite prefix set at the least available
index gives a finite nonempty subset of each member of the original family. -/
theorem countableMultipleChoice_of_unbounded_prefix_choices
    (A : ℕ → Type u) (S : Set ℕ)
    (hS : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ n ∈ S)
    (F : (n : ℕ) → Set (ChoicePrefix A n))
    (hF : ∀ n ∈ S, (F n).Finite ∧ (F n).Nonempty) :
    ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty := by
  classical
  let m : ℕ → ℕ := fun k => Nat.find (hS k)
  have hm (k : ℕ) : k ≤ m k ∧ m k ∈ S := Nat.find_spec (hS k)
  let evaluate (k : ℕ) (b : ChoicePrefix A (m k)) : A k :=
    b ⟨k, Nat.lt_succ_of_le (hm k).1⟩
  refine ⟨fun k => evaluate k '' F (m k), ?_⟩
  intro k
  obtain ⟨hfinite, hnonempty⟩ := hF (m k) (hm k).2
  exact ⟨hfinite.image (evaluate k), hnonempty.image (evaluate k)⟩

/-- If a family has no countable multiple choice, no unbounded set of its
finite prefixes admits an actual family of nonempty finite subsets. -/
theorem not_unbounded_prefix_choices_of_not_countableMultipleChoice
    (A : ℕ → Type u)
    (hA : ¬ ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty)
    (S : Set ℕ) (hS : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ n ∈ S)
    (F : (n : ℕ) → Set (ChoicePrefix A n)) :
    ¬ ∀ n ∈ S, (F n).Finite ∧ (F n).Nonempty := by
  intro hF
  exact hA (countableMultipleChoice_of_unbounded_prefix_choices A S hS F hF)

end Adiabatic.Foundations
