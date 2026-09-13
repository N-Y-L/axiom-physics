import Adiabatic.Unbounded.Resolvent
import Adiabatic.Unbounded.TimeSlicing
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniform graph norm bounds for frozen evolution products

A continuously differentiable common-domain Hamiltonian has uniformly comparable
shifted graph norms. Each frozen unitary preserves its own graph norm; adjacent
changes therefore accumulate through total variation of the sample times.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)

/-- Resolvents at i are uniformly bounded into the common Banach domain. -/
theorem exists_uniform_inverseShift_bound
    (hc : ContinuousOn H (Icc (0 : ℝ) 1))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖domain.inverseShift (H t) Complex.I‖ ≤ M := by
  have hR : ContinuousOn (fun t => domain.inverseShift (H t) Complex.I) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((domain.inverseShift_contDiffAt_operator (H t) Complex.I
      (domain.mem_resolventSet_of_im_ne_zero (H t) (hH t ht) Complex.I (by simp)) 0).continuousAt).comp_continuousWithinAt (hc t ht)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

/-- Operator differences composed with any reference resolvent are uniformly Lipschitz. -/
theorem exists_uniform_relative_difference_bound
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ q ∈ Icc (0 : ℝ) 1,
        ‖(H t - H s).comp (domain.inverseShift (H q) Complex.I)‖ ≤ L * |t - s| := by
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨M, hM, hb⟩ := domain.exists_uniform_inverseShift_bound H hc.continuousOn hH
  refine ⟨K * M, mul_nonneg K.coe_nonneg hM, ?_⟩
  intro s hs t ht q hq
  have hd : ‖H t - H s‖ ≤ K * |t - s| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hK.dist_le_mul t ht s hs
  calc
    ‖(H t - H s).comp (domain.inverseShift (H q) Complex.I)‖ ≤
        ‖H t - H s‖ * ‖domain.inverseShift (H q) Complex.I‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (K * |t - s|) * M := mul_le_mul hd (hb q hq) (norm_nonneg _) (by positivity)
    _ = (K * M) * |t - s| := by ring

/-- Adjacent graph norms differ by at most a linear factor in elapsed time. -/
theorem exists_shifted_graph_change_bound
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖ := by
  obtain ⟨L, hL, hb⟩ := domain.exists_uniform_relative_difference_bound H hc hH
  refine ⟨L, hL, ?_⟩
  intro s hs t ht x
  have hp := domain.mem_resolventSet_of_im_ne_zero (H s) (hH s hs) Complex.I (by simp)
  have heq : domain.shift (H t) Complex.I x = domain.shift (H s) Complex.I x +
      ((H t - H s).comp (domain.inverseShift (H s) Complex.I))
        (domain.shift (H s) Complex.I x) := by
    rw [ContinuousLinearMap.comp_apply, domain.inverseShift_shift (H s) Complex.I hp]
    simp only [shift_apply, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖domain.shift (H s) Complex.I x‖ +
        ‖((H t - H s).comp (domain.inverseShift (H s) Complex.I))
          (domain.shift (H s) Complex.I x)‖ := norm_add_le _ _
    _ ≤ ‖domain.shift (H s) Complex.I x‖ +
        (L * |t - s|) * ‖domain.shift (H s) Complex.I x‖ := by
      gcongr
      exact ContinuousLinearMap.le_of_opNorm_le _ (hb s hs t ht s hs) _
    _ = _ := by ring

omit [CompleteSpace D] [CompleteSpace E] in
/-- Frozen evolution products accumulate graph growth only through sample-time variation. -/
theorem norm_shift_timeOrderedProduct_le_exp_sum (L : ℝ) (_hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ ≤
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ) (x : D) :
    ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ ≤
      Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
        ‖domain.shift (H (τ 0)) Complex.I x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [timeOrderedProduct_succ, ContinuousLinearMap.mul_apply]
    calc
      _ ≤ (1 + L * |τ (n + 1) - τ n|) *
          ‖domain.shift (H (τ n)) Complex.I (v n (timeOrderedProduct v n x))‖ :=
        hchange (τ n) (hτ n) (τ (n + 1)) (hτ (n + 1)) _
      _ ≤ Real.exp (L * |τ (n + 1) - τ n|) *
          (Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
            ‖domain.shift (H (τ 0)) Complex.I x‖) := by
        apply mul_le_mul
          (by simpa [add_comm] using Real.add_one_le_exp (L * |τ (n + 1) - τ n|))
          ((hv n _).trans ih) (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← mul_assoc, ← Real.exp_add, Finset.sum_range_succ]; congr 2; ring

omit [CompleteSpace D] in
/-- The physical unitary intertwining identity supplies the frozen graph contraction. -/
theorem norm_shift_timeOrderedProduct_le_of_unitary (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1)
    (u : ℕ → E →L[ℂ] E) (v : ℕ → D →L[ℂ] D)
    (hu : ∀ n, u n ∈ unitary (E →L[ℂ] E))
    (hv : ∀ n x, domain.shift (H (τ n)) Complex.I (v n x) =
      u n (domain.shift (H (τ n)) Complex.I x)) (n : ℕ) (x : D) :
    ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ ≤
      Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
        ‖domain.shift (H (τ 0)) Complex.I x‖ := by
  apply domain.norm_shift_timeOrderedProduct_le_exp_sum H L hL hchange τ hτ v _ n x
  intro k y
  rw [hv, ContinuousLinearMap.norm_map_of_mem_unitary (hu k)]

omit [CompleteSpace D] [CompleteSpace E] in
/-- Graph bounds for a subproduct with arbitrary physical initial and final times. -/
theorem norm_shift_timeOrderedProduct_le_endpoints (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ ≤
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ)
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ ≤
      Real.exp (L * (|t - τ n| +
        ∑ k ∈ Finset.range n, |τ (k + 1) - τ k| + |τ 0 - s|)) *
          ‖domain.shift (H s) Complex.I x‖ := by
  have hexp (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
      (y : D) : ‖domain.shift (H b) Complex.I y‖ ≤
        Real.exp (L * |b - a|) * ‖domain.shift (H a) Complex.I y‖ := by
    exact (hchange a ha b hb y).trans (mul_le_mul_of_nonneg_right
      (by simpa [add_comm] using Real.add_one_le_exp (L * |b - a|)) (norm_nonneg _))
  calc
    _ ≤ Real.exp (L * |t - τ n|) *
        ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ :=
      hexp (τ n) t (hτ n) ht _
    _ ≤ Real.exp (L * |t - τ n|) *
        (Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
          (Real.exp (L * |τ 0 - s|) * ‖domain.shift (H s) Complex.I x‖)) := by
      gcongr
      exact (domain.norm_shift_timeOrderedProduct_le_exp_sum H L hL hchange τ hτ v hv n x).trans
        (mul_le_mul_of_nonneg_left (hexp s (τ 0) hs (hτ 0) x) (Real.exp_nonneg _))
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

omit [CompleteSpace D] [CompleteSpace E] in
/-- Monotone floor samples give a two-time bound with only two mesh errors. -/
theorem norm_shift_timeOrderedProduct_le_mesh (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1) (hmono : Monotone τ)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ ≤
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ)
    (s t mesh : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) (hstart : τ 0 ≤ s) (hend : τ n ≤ t) (hmesh : s - τ 0 ≤ mesh)
    (x : D) :
    ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ ≤
      Real.exp (L * (|t - s| + 2 * mesh)) * ‖domain.shift (H s) Complex.I x‖ := by
  have hsum : (∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) = τ n - τ 0 := by
    calc
      _ = ∑ k ∈ Finset.range n, (τ (k + 1) - τ k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ k)))
      _ = _ := Finset.sum_range_sub τ n
  apply (domain.norm_shift_timeOrderedProduct_le_endpoints H L hL hchange τ hτ v hv
    n s t hs ht x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hL
  rw [hsum, abs_of_nonneg (sub_nonneg.mpr hend), abs_of_nonpos (sub_nonpos.mpr hstart),
    abs_of_nonneg (sub_nonneg.mpr hst)]
  linarith

omit [CompleteSpace D] [CompleteSpace E] in
/-- Reversed floor samples obey the same two-time mesh bound. -/
theorem norm_shift_timeOrderedProduct_le_mesh_reverse (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1) (hanti : Antitone τ)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ ≤
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ)
    (s t mesh : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : t ≤ s) (hstart : τ 0 ≤ s) (hend : τ n ≤ t) (hmesh : t - τ n ≤ mesh)
    (x : D) :
    ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ ≤
      Real.exp (L * (|t - s| + 2 * mesh)) * ‖domain.shift (H s) Complex.I x‖ := by
  have hsum : (∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) = τ 0 - τ n := by
    calc
      _ = ∑ k ∈ Finset.range n, (τ k - τ (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ k)))]
        ring
      _ = - ∑ k ∈ Finset.range n, (τ (k + 1) - τ k) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [Finset.sum_range_sub τ n]; ring
  apply (domain.norm_shift_timeOrderedProduct_le_endpoints H L hL hchange τ hτ v hv
    n s t hs ht x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hL
  rw [hsum, abs_of_nonneg (sub_nonneg.mpr hend), abs_of_nonpos (sub_nonpos.mpr hstart),
    abs_of_nonpos (sub_nonpos.mpr hst)]
  linarith

/-- Uniform graph control converts to an operator bound on the Banach common domain. -/
theorem norm_timeOrderedProduct_le_of_graph_bound
    (t : ℝ) (hH : domain.IsSelfAdjoint (H t)) (v : ℕ → D →L[ℂ] D) (n : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ ≤ C * ‖x‖) :
    ‖timeOrderedProduct v n‖ ≤ ‖domain.inverseShift (H t) Complex.I‖ * C := by
  have hp := domain.mem_resolventSet_of_im_ne_zero (H t) hH Complex.I (by simp)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hC)
  intro x
  calc
    ‖timeOrderedProduct v n x‖ =
        ‖domain.inverseShift (H t) Complex.I
          (domain.shift (H t) Complex.I (timeOrderedProduct v n x))‖ := by
      rw [domain.inverseShift_shift (H t) Complex.I hp]
    _ ≤ ‖domain.inverseShift (H t) Complex.I‖ *
        ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)

omit [CompleteSpace D] [CompleteSpace E] in
/-- A frozen product also controls its input graph norm in terms of its
output graph norm, with the same total-variation constant. -/
theorem norm_shift_le_exp_sum_timeOrderedProduct (L : ℝ) (_hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ =
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ) (x : D) :
    ‖domain.shift (H (τ 0)) Complex.I x‖ ≤
      Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
        ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ ≤
        Real.exp (L * |τ (n + 1) - τ n|) *
          ‖domain.shift (H (τ (n + 1))) Complex.I (timeOrderedProduct v (n + 1) x)‖ := by
      rw [timeOrderedProduct_succ, ContinuousLinearMap.mul_apply, ← hv n]
      apply (hchange (τ (n + 1)) (hτ (n + 1)) (τ n) (hτ n) _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [abs_sub_comm]
      simpa [add_comm] using Real.add_one_le_exp (L * |τ (n + 1) - τ n|)
    calc
      _ ≤ Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
          ‖domain.shift (H (τ n)) Complex.I (timeOrderedProduct v n x)‖ := ih
      _ ≤ Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
          (Real.exp (L * |τ (n + 1) - τ n|) *
            ‖domain.shift (H (τ (n + 1))) Complex.I (timeOrderedProduct v (n + 1) x)‖) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add, Finset.sum_range_succ]
        congr 2
        ring

omit [CompleteSpace D] [CompleteSpace E] in
/-- The endpoint graph estimate also bounds the input by the output. -/
theorem norm_shift_le_endpoints_timeOrderedProduct (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ =
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ)
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    ‖domain.shift (H s) Complex.I x‖ ≤
      Real.exp (L * (|t - τ n| +
        ∑ k ∈ Finset.range n, |τ (k + 1) - τ k| + |τ 0 - s|)) *
          ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ := by
  have hexp (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
      (y : D) : ‖domain.shift (H b) Complex.I y‖ ≤
        Real.exp (L * |b - a|) * ‖domain.shift (H a) Complex.I y‖ := by
    exact (hchange a ha b hb y).trans (mul_le_mul_of_nonneg_right
      (by simpa [add_comm] using Real.add_one_le_exp (L * |b - a|)) (norm_nonneg _))
  calc
    _ ≤ Real.exp (L * |s - τ 0|) * ‖domain.shift (H (τ 0)) Complex.I x‖ :=
      hexp (τ 0) s (hτ 0) hs x
    _ ≤ Real.exp (L * |s - τ 0|) *
        (Real.exp (L * ∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) *
          (Real.exp (L * |τ n - t|) *
            ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact (domain.norm_shift_le_exp_sum_timeOrderedProduct H L hL hchange τ hτ v hv n x).trans
        (mul_le_mul_of_nonneg_left (hexp t (τ n) ht (hτ n) _) (Real.exp_nonneg _))
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add,
        abs_sub_comm s, abs_sub_comm (τ n)]
      congr 2
      ring

omit [CompleteSpace D] [CompleteSpace E] in
/-- Monotone floor samples give the same sharp mesh estimate for an inverse
product by bounding the initial vector through the final vector. -/
theorem norm_shift_le_mesh_timeOrderedProduct (L : ℝ) (hL : 0 ≤ L)
    (hchange : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + L * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc (0 : ℝ) 1) (hmono : Monotone τ)
    (v : ℕ → D →L[ℂ] D)
    (hv : ∀ n x, ‖domain.shift (H (τ n)) Complex.I (v n x)‖ =
      ‖domain.shift (H (τ n)) Complex.I x‖) (n : ℕ)
    (s t mesh : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) (hstart : τ 0 ≤ s) (hend : τ n ≤ t) (hmesh : s - τ 0 ≤ mesh)
    (x : D) :
    ‖domain.shift (H s) Complex.I x‖ ≤ Real.exp (L * (|t - s| + 2 * mesh)) *
      ‖domain.shift (H t) Complex.I (timeOrderedProduct v n x)‖ := by
  have hsum : (∑ k ∈ Finset.range n, |τ (k + 1) - τ k|) = τ n - τ 0 := by
    calc
      _ = ∑ k ∈ Finset.range n, (τ (k + 1) - τ k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ k)))
      _ = _ := Finset.sum_range_sub τ n
  apply (domain.norm_shift_le_endpoints_timeOrderedProduct H L hL hchange τ hτ v hv
    n s t hs ht x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hL
  rw [hsum, abs_of_nonneg (sub_nonneg.mpr hend), abs_of_nonpos (sub_nonpos.mpr hstart),
    abs_of_nonneg (sub_nonneg.mpr hst)]
  linarith

end Adiabatic.Unbounded.CommonDomain
