import Adiabatic.Unbounded.FrozenGraphBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A complete family of frozen common-domain approximations

Continuous differentiability and genuine self-adjointness provide the
frozen evolutions, a vanishing uniform coefficient error, and domain bounds
independent of the number of time slices.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Filter
open scoped Topology

/-- The uniform time grids become arbitrarily fine. -/
theorem tendsto_gridMesh : Tendsto gridMesh atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ))
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E) (z : ℂ)

/-- All estimates required to pass frozen evolutions to a strong limit. -/
structure FrozenApproximation where
  family : ∀ n, FrozenFamily domain H z n
  error : ℕ → ℝ
  error_nonneg : ∀ n, 0 ≤ error n
  error_limit : Tendsto error atTop (𝓝 0)
  error_bound : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖stepHamiltonian H n t - H t‖ ≤ error n
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  forward_bound : ∀ n t, ‖(family n).lift t‖ ≤ bound
  inverse_bound : ∀ n t, ‖(family n).inverseLift t‖ ≤ bound
  graph_constant : ℝ
  graph_constant_nonneg : 0 ≤ graph_constant
  graph_change : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
    ‖domain.shift (H t) Complex.I x‖ ≤
      (1 + graph_constant * |t - s|) * ‖domain.shift (H s) Complex.I x‖

/-- A C¹ self-adjoint common-domain family has frozen approximations with
all uniform estimates derived from its stated hypotheses. -/
theorem exists_frozenApproximation
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (hz : star z = -z) : Nonempty (FrozenApproximation domain H z) := by
  let V := fun n => Classical.choice (exists_frozenFamily domain H hH z hz n)
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨L, hL, hchange⟩ := domain.exists_shifted_graph_change_bound H hc hH
  let Bf := ‖domain.inverseShift (H 1) Complex.I‖ *
    (Real.exp L * ‖domain.shift (H 0) Complex.I‖)
  let Bi := ‖domain.inverseShift (H 0) Complex.I‖ *
    (Real.exp L * ‖domain.shift (H 1) Complex.I‖)
  refine ⟨{
    family := V
    error := fun n => K * gridMesh n
    error_nonneg := fun n => mul_nonneg K.coe_nonneg (gridMesh_pos n).le
    error_limit := by simpa using tendsto_gridMesh.const_mul (K : ℝ)
    error_bound := fun n _ ht => norm_stepHamiltonian_sub_le H hK n ht
    bound := max Bf Bi
    bound_nonneg := (show 0 ≤ Bf by positivity).trans (le_max_left _ _)
    forward_bound := fun n t => ((V n).norm_lift_le (hH 1 (by simp)) L hL hchange t).trans
      (le_max_left _ _)
    inverse_bound := fun n t => ((V n).norm_inverseLift_le (hH 0 (by simp)) L hL hchange t).trans
      (le_max_right _ _)
    graph_constant := L
    graph_constant_nonneg := hL
    graph_change := hchange
  }⟩

end Adiabatic.Unbounded
