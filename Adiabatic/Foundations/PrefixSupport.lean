import Adiabatic.Foundations.PrefixMultipleChoice
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Finite active prefix levels under failure of countable multiple choice

A summable nonnegative scalar family has finite positive-threshold sets.
At each active prefix level we take the least reciprocal-integer threshold
with a nonempty set. If the active levels were unbounded, projecting these
finite nonempty prefix sets would give countable multiple choice.

The coefficient family can be the squared absolute values of coordinates
of a square-summable vector. The proof uses actual finite threshold sets;
it does not invoke a global choice function for the original family.
-/

namespace Adiabatic.Foundations

universe u v

/-- A level is active when at least one coefficient at that level is nonzero. -/
def activePrefixLevels (A : ℕ → Type u) {β : Type v} [Zero β]
    (c : (Σ n, ChoicePrefix A n) → β) : Set ℕ :=
  {n | ∃ b : ChoicePrefix A n, c ⟨n, b⟩ ≠ 0}

/-- Summability makes every positive upper-threshold set finite. -/
theorem finite_positive_threshold_of_summable
    {X : Type u} (c : X → ℝ) (hc : Summable c)
    (ε : ℝ) (hε : 0 < ε) : {x | ε ≤ c x}.Finite := by
  have heventually : ∀ᶠ x in Filter.cofinite, c x < ε :=
    hc.tendsto_cofinite_zero.eventually_lt_const hε
  simpa only [Filter.Eventually, Filter.mem_cofinite, Set.compl_setOf, not_lt]
    using heventually

/-- Unbounded active levels of a summable nonnegative prefix family provide
actual finite nonempty subsets of all members of the original family. -/
theorem countableMultipleChoice_of_unbounded_active_prefix_levels
    (A : ℕ → Type u) (c : (Σ n, ChoicePrefix A n) → ℝ)
    (hc : Summable c) (hc_nonneg : ∀ x, 0 ≤ c x)
    (hactive : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ n ∈ activePrefixLevels A c) :
    ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty := by
  classical
  have hthreshold (n : ℕ) (hn : n ∈ activePrefixLevels A c) :
      ∃ m : ℕ, ∃ b : ChoicePrefix A n, 1 / (m + 1 : ℝ) ≤ c ⟨n, b⟩ := by
    obtain ⟨b, hb⟩ := hn
    have hbpos : 0 < c ⟨n, b⟩ := lt_of_le_of_ne (hc_nonneg _) (Ne.symm hb)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hbpos
    exact ⟨m, b, le_of_lt hm⟩
  let threshold (n m : ℕ) : Set (ChoicePrefix A n) :=
    {b | 1 / (m + 1 : ℝ) ≤ c ⟨n, b⟩}
  let F (n : ℕ) : Set (ChoicePrefix A n) :=
    if hn : n ∈ activePrefixLevels A c then
      threshold n (Nat.find (hthreshold n hn))
    else ∅
  apply countableMultipleChoice_of_unbounded_prefix_choices A
    (activePrefixLevels A c) hactive F
  intro n hn
  simp only [F, dif_pos hn]
  constructor
  · have hpos : 0 < 1 / (Nat.find (hthreshold n hn) + 1 : ℝ) := by
      positivity
    have hfinite := finite_positive_threshold_of_summable c hc
      (1 / (Nat.find (hthreshold n hn) + 1 : ℝ)) hpos
    exact hfinite.preimage
      (f := fun b : ChoicePrefix A n => (⟨n, b⟩ : Σ n, ChoicePrefix A n))
      (fun _ _ _ _ h => by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h)
  · exact Nat.find_spec (hthreshold n hn)

/-- Under failure of countable multiple choice for `A`, a summable
nonnegative coefficient family has only finitely many active prefix levels. -/
theorem finite_active_levels_of_not_countableMultipleChoice
    (A : ℕ → Type u)
    (hA : ¬ ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty)
    (c : (Σ n, ChoicePrefix A n) → ℝ)
    (hc : Summable c) (hc_nonneg : ∀ x, 0 ≤ c x) :
    (activePrefixLevels A c).Finite := by
  classical
  by_contra hinfinite
  apply hA
  apply countableMultipleChoice_of_unbounded_active_prefix_levels A c hc hc_nonneg
  intro k
  obtain ⟨n, hn, hkn⟩ := Set.Infinite.exists_gt hinfinite k
  exact ⟨n, le_of_lt hkn, hn⟩

/-- In particular, the nonzero levels of an actual square-summable vector
are finite. This applies to complex coordinates without choosing an
enumeration of their support. -/
theorem finite_active_levels_of_square_summable_of_not_countableMultipleChoice
    (A : ℕ → Type u)
    (hA : ¬ ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty)
    {β : Type v} [NormedAddGroup β]
    (c : (Σ n, ChoicePrefix A n) → β)
    (hc : Summable (fun x => ‖c x‖ ^ 2)) :
    (activePrefixLevels A c).Finite := by
  have hfinite := finite_active_levels_of_not_countableMultipleChoice
    A hA (fun x => ‖c x‖ ^ 2) hc (fun x => sq_nonneg ‖c x‖)
  simpa only [activePrefixLevels, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hfinite

/-- The finite-level conclusion supplies the bound needed to compare a
level-weighted norm with the ordinary norm for this particular vector. -/
theorem bounded_active_levels_of_square_summable_of_not_countableMultipleChoice
    (A : ℕ → Type u)
    (hA : ¬ ∃ G : (k : ℕ) → Set (A k), ∀ k, (G k).Finite ∧ (G k).Nonempty)
    {β : Type v} [NormedAddGroup β]
    (c : (Σ n, ChoicePrefix A n) → β)
    (hc : Summable (fun x => ‖c x‖ ^ 2)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ b : ChoicePrefix A n, c ⟨n, b⟩ = 0 := by
  classical
  have hfinite :=
    finite_active_levels_of_square_summable_of_not_countableMultipleChoice A hA c hc
  refine ⟨hfinite.toFinset.sup id, ?_⟩
  intro n hn b
  by_contra hb
  have hmem : n ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨b, hb⟩
  have hle : n ≤ hfinite.toFinset.sup id := Finset.le_sup (f := id) hmem
  exact (not_le_of_gt hn) hle

end Adiabatic.Foundations
