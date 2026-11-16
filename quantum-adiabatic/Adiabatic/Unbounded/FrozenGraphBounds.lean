import Adiabatic.Unbounded.FrozenEvolution
import Adiabatic.Unbounded.GraphBounds

/-!
# Uniform common-domain bounds for frozen evolutions

The shifted graph norm changes only when the frozen sample changes.
Consequently products stay bounded in the common domain independently of
the number of time slices.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set

@[simp] theorem gridSample_zero (n : ℕ) : gridSample n 0 = 0 := by
  simp [gridSample]

@[simp] theorem gridSample_last (n : ℕ) : gridSample n (n + 1) = 1 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [gridSample, gridMesh, hn]

theorem gridSample_monotone (n : ℕ) : Monotone (gridSample n) := by
  intro k l hkl
  apply min_le_min _ le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) (gridMesh_pos n).le

theorem sum_gridSample_variation (n m : ℕ) :
    (∑ k ∈ Finset.range m, |gridSample n (k + 1) - gridSample n k|) =
      gridSample n m := by
  calc
    _ = ∑ k ∈ Finset.range m, (gridSample n (k + 1) - gridSample n k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact abs_of_nonneg (sub_nonneg.mpr (gridSample_monotone n (Nat.le_succ k)))
    _ = _ := by rw [Finset.sum_range_sub, gridSample_zero, sub_zero]

theorem gridIndex_monotone (n : ℕ) : Monotone (gridIndex n) := by
  intro s t hst
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _))

theorem gridIndex_le_last {n : ℕ} {t : ℝ} (ht : t ≤ 1) : gridIndex n t ≤ n + 1 := by
  have hm := gridIndex_monotone n ht
  have he : gridIndex n 1 = n + 1 := by simp only [gridIndex, mul_one, Nat.floor_natCast]
  rwa [he] at hm

/-- Sample times clamped to the cells that can change between two times. -/
def transitionSample (n : ℕ) (s t : ℝ) (k : ℕ) : ℝ :=
  gridSample n (max (gridIndex n s) (min k (gridIndex n t)))

theorem transitionSample_mem (n : ℕ) (s t : ℝ) (k : ℕ) :
    transitionSample n s t k ∈ Icc (0 : ℝ) 1 := gridSample_mem n _

theorem transitionSample_monotone (n : ℕ) (s t : ℝ) : Monotone (transitionSample n s t) := by
  intro a b hab
  exact gridSample_monotone n (max_le_max le_rfl (min_le_min hab le_rfl))

@[simp] theorem transitionSample_zero (n : ℕ) (s t : ℝ) :
    transitionSample n s t 0 = gridSample n (gridIndex n s) := by
  simp [transitionSample]

theorem transitionSample_last {n : ℕ} {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1) :
    transitionSample n s t (n + 1) = gridSample n (gridIndex n t) := by
  rw [transitionSample, min_eq_right (gridIndex_le_last ht),
    max_eq_right (gridIndex_monotone n hst)]

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {z : ℂ} {n : ℕ}

namespace FrozenFamily

variable (V : FrozenFamily domain H z n)

omit [CompleteSpace D] in
/-- Every clipped forward product has the same one-interval graph bound. -/
theorem norm_shift_lift_le (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (t : ℝ) (x : D) :
    ‖domain.shift (H 1) Complex.I (V.lift t x)‖ ≤
      Real.exp L * ‖domain.shift (H 0) Complex.I x‖ := by
  have hv : ∀ k y, ‖domain.shift (H (gridSample n k)) Complex.I
      ((V.propagator k).lift (gridDuration n k t) y)‖ ≤
        ‖domain.shift (H (gridSample n k)) Complex.I y‖ := by
    intro k y
    rw [V.shift_lift k (gridDuration n k t),
      ContinuousLinearMap.norm_map_of_mem_unitary
        ((V.propagator k).isUnitary _)]
  simpa only [lift, gridSample_last, gridSample_zero, sum_gridSample_variation, mul_one] using
    domain.norm_shift_timeOrderedProduct_le_exp_sum H L hL hchange (gridSample n)
      (gridSample_mem n) (fun k => (V.propagator k).lift (gridDuration n k t)) hv (n + 1) x

/-- The forward domain norm bound is independent of the time grid and the
physical time. -/
theorem norm_lift_le (hH : domain.IsSelfAdjoint (H 1)) (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (t : ℝ) :
    ‖V.lift t‖ ≤ ‖domain.inverseShift (H 1) Complex.I‖ *
      (Real.exp L * ‖domain.shift (H 0) Complex.I‖) := by
  apply domain.norm_timeOrderedProduct_le_of_graph_bound H 1 hH _ (n + 1)
    (Real.exp L * ‖domain.shift (H 0) Complex.I‖) (by positivity)
  intro x
  calc
    _ ≤ Real.exp L * ‖domain.shift (H 0) Complex.I x‖ := V.norm_shift_lift_le L hL hchange t x
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_nonneg _)

omit [CompleteSpace D] in
/-- The inverse clipped product has the same one-interval graph bound. -/
theorem norm_shift_inverseLift_le (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (t : ℝ) (x : D) :
    ‖domain.shift (H 0) Complex.I (V.inverseLift t x)‖ ≤
      Real.exp L * ‖domain.shift (H 1) Complex.I x‖ := by
  have hv : ∀ k y, ‖domain.shift (H (gridSample n k)) Complex.I
      ((V.propagator k).lift (gridDuration n k t) y)‖ =
        ‖domain.shift (H (gridSample n k)) Complex.I y‖ := by
    intro k y
    rw [V.shift_lift, ContinuousLinearMap.norm_map_of_mem_unitary
      ((V.propagator k).isUnitary _)]
  have hb := domain.norm_shift_le_exp_sum_timeOrderedProduct H L hL hchange (gridSample n)
    (gridSample_mem n) (fun k => (V.propagator k).lift (gridDuration n k t)) hv
    (n + 1) (V.inverseLift t x)
  change ‖domain.shift (H (gridSample n 0)) Complex.I (V.inverseLift t x)‖ ≤
    Real.exp (L * ∑ k ∈ Finset.range (n + 1), |gridSample n (k + 1) - gridSample n k|) *
      ‖domain.shift (H (gridSample n (n + 1))) Complex.I (V.lift t (V.inverseLift t x))‖ at hb
  simpa only [gridSample_last, gridSample_zero, sum_gridSample_variation, mul_one,
    V.lift_inverseLift] using hb

/-- The inverse domain bound is also independent of the grid and time. -/
theorem norm_inverseLift_le (hH : domain.IsSelfAdjoint (H 0)) (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (t : ℝ) :
    ‖V.inverseLift t‖ ≤ ‖domain.inverseShift (H 0) Complex.I‖ *
      (Real.exp L * ‖domain.shift (H 1) Complex.I‖) := by
  have hp := domain.mem_resolventSet_of_im_ne_zero (H 0) hH Complex.I (by simp)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖V.inverseLift t x‖ = ‖domain.inverseShift (H 0) Complex.I
        (domain.shift (H 0) Complex.I (V.inverseLift t x))‖ := by
      rw [domain.inverseShift_shift _ _ hp]
    _ ≤ ‖domain.inverseShift (H 0) Complex.I‖ *
        ‖domain.shift (H 0) Complex.I (V.inverseLift t x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖domain.inverseShift (H 0) Complex.I‖ *
        (Real.exp L * ‖domain.shift (H 1) Complex.I x‖) :=
      mul_le_mul_of_nonneg_left (V.norm_shift_inverseLift_le L hL hchange t x) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_nonneg _))
        (norm_nonneg _)

omit [CompleteSpace D] in
/-- A difference-time factor preserves the graph norm of its clamped
sample; outside the active cells it is the identity. -/
theorem norm_duration_difference_shift {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (k : ℕ) (x : D) :
    ‖domain.shift (H (transitionSample n s t k)) Complex.I
      ((V.propagator k).lift (gridDuration n k t - gridDuration n k s) x)‖ =
        ‖domain.shift (H (transitionSample n s t k)) Complex.I x‖ := by
  by_cases hlo : gridIndex n s ≤ k
  · by_cases hhi : k ≤ gridIndex n t
    · rw [transitionSample, min_eq_left hhi, max_eq_right hlo, V.shift_lift,
        ContinuousLinearMap.norm_map_of_mem_unitary ((V.propagator k).isUnitary _)]
    · have hk : gridIndex n t < k := Nat.lt_of_not_ge hhi
      have hb := (gridIndex_bounds (n := n) ht.1).2.le
      rw [gridDuration_future hk hb, gridDuration_future hk (hst.trans hb), sub_self,
        V.factor_lift_zero, ContinuousLinearMap.one_apply]
  · have hk : k < gridIndex n s := Nat.lt_of_not_ge hlo
    have hb := (gridIndex_bounds (n := n) hs.1).1
    rw [gridDuration_full hk (hb.trans hst), gridDuration_full hk hb, sub_self,
      V.factor_lift_zero, ContinuousLinearMap.one_apply]

omit [CompleteSpace D] in
/-- Difference-time products have a sharp graph bound depending only on
the elapsed physical time and two mesh errors. -/
theorem norm_shift_duration_difference_product_le (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (x : D) :
    ‖domain.shift (H t) Complex.I
      (timeOrderedProduct (fun k => (V.propagator k).lift
        (gridDuration n k t - gridDuration n k s)) (n + 1) x)‖ ≤
      Real.exp (L * (|t - s| + 2 * gridMesh n)) * ‖domain.shift (H s) Complex.I x‖ := by
  have hlo := gridSample_index_bounds (n := n) hs
  have hhi := gridSample_index_bounds (n := n) ht
  apply domain.norm_shift_timeOrderedProduct_le_mesh H L hL hchange
    (transitionSample n s t) (transitionSample_mem n s t) (transitionSample_monotone n s t)
    _ (fun k y => (V.norm_duration_difference_shift hs ht hst k y).le) (n + 1)
    s t (gridMesh n) hs ht hst
  · simpa only [transitionSample_zero] using hlo.1
  · simpa only [transitionSample_last hst ht.2] using hhi.1
  · simpa only [transitionSample_zero, abs_of_nonpos (sub_nonpos.mpr hlo.1), neg_sub] using hlo.2

omit [CompleteSpace D] in
/-- The matching inverse graph bound for a difference-time product. -/
theorem norm_shift_le_duration_difference_product (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (x : D) :
    ‖domain.shift (H s) Complex.I x‖ ≤ Real.exp (L * (|t - s| + 2 * gridMesh n)) *
      ‖domain.shift (H t) Complex.I
        (timeOrderedProduct (fun k => (V.propagator k).lift
          (gridDuration n k t - gridDuration n k s)) (n + 1) x)‖ := by
  have hlo := gridSample_index_bounds (n := n) hs
  have hhi := gridSample_index_bounds (n := n) ht
  apply domain.norm_shift_le_mesh_timeOrderedProduct H L hL hchange
    (transitionSample n s t) (transitionSample_mem n s t) (transitionSample_monotone n s t)
    _ (V.norm_duration_difference_shift hs ht hst) (n + 1) s t (gridMesh n) hs ht hst
  · simpa only [transitionSample_zero] using hlo.1
  · simpa only [transitionSample_last hst ht.2] using hhi.1
  · simpa only [transitionSample_zero, abs_of_nonpos (sub_nonpos.mpr hlo.1), neg_sub] using hlo.2

omit [CompleteSpace D] in
/-- Frozen two-time evolution obeys the sharp shifted graph bound in both
time directions. The two mesh errors vanish in the limiting propagator. -/
theorem norm_shift_transition_le (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    ‖domain.shift (H t) Complex.I (V.lift t (V.inverseLift s x))‖ ≤
      Real.exp (L * (|t - s| + 2 * gridMesh n)) * ‖domain.shift (H s) Complex.I x‖ := by
  by_cases hst : s ≤ t
  · rw [V.lift_inverseLift_eq_increment hst]
    exact V.norm_shift_duration_difference_product_le L hL hchange hs ht hst x
  · have hts := (lt_of_not_ge hst).le
    have hb := V.norm_shift_le_duration_difference_product L hL hchange ht hs hts
      (V.lift t (V.inverseLift s x))
    rw [← V.lift_inverseLift_eq_increment hts, V.inverseLift_lift, V.lift_inverseLift] at hb
    simpa only [abs_sub_comm s t] using hb

end FrozenFamily
end Adiabatic.Unbounded
