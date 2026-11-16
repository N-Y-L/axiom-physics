/-
The factorial Picard-iterate argument below is adapted from
Mathlib.Analysis.ODE.PicardLindelof, copyright (c) 2021 Yury Kudryashov,
authors Yury Kudryashov and Winston Yin, released under the Apache 2.0 license.
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Existence of propagators on a compact time interval

For a vector field globally Lipschitz in the state, Picard iteration acts on
all continuous curves on `[0, 1]`. Its iterates have factorially decaying
Lipschitz constants. A contracting iterate supplies a fixed point,
with no smallness condition on the coefficient norm.
-/

namespace Adiabatic

open Set Metric Function MeasureTheory
open scoped Nat NNReal Topology

namespace PropagatorConstruction

variable {E : Type*} [NormedAddCommGroup E]

abbrev Curve (E : Type*) [TopologicalSpace E] := C(Icc (0 : ℝ) 1, E)

noncomputable def extend (α : Curve E) (t : ℝ) : E :=
  α (projIcc 0 1 zero_le_one t)

@[simp] lemma extend_val (α : Curve E) (t : Icc (0 : ℝ) 1) :
    extend α t = α t := by simp [extend]

lemma extend_of_mem (α : Curve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extend α t = α ⟨t, ht⟩ := by simp [extend, projIcc_of_mem _ ht]

lemma continuous_extend (α : Curve E) : Continuous (extend α) :=
  α.continuous.comp continuous_projIcc

variable [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E}
  (hf : ContinuousOn (uncurry f) (Icc (0 : ℝ) 1 ×ˢ (univ : Set E)))

include hf

omit [CompleteSpace E] in
lemma continuousOn_comp (α : Curve E) :
    ContinuousOn (fun t => f t (extend α t)) (Icc (0 : ℝ) 1) :=
  ODE.continuousOn_comp hf (continuous_extend α).continuousOn (fun _ _ => mem_univ _)

omit [CompleteSpace E] in
lemma intervalIntegrable_comp (α : Curve E) (t : Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => f s (extend α s)) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_comp hf α).mono
  rw [uIcc_of_le t.2.1]
  exact Icc_subset_Icc le_rfl t.2.2

lemma picard_deriv (x₀ : E) (α : Curve E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (ODE.picard f 0 x₀ (extend α)) (f t (extend α t))
      (Icc (0 : ℝ) 1) t :=
  ODE.hasDerivWithinAt_picard_Icc (by simp) hf
    (continuous_extend α).continuousOn (by simp) x₀ ht

noncomputable def next (x₀ : E) (α : Curve E) : Curve E where
  toFun t := ODE.picard f 0 x₀ (extend α) t
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (fun _ ht => (picard_deriv hf x₀ α ht).continuousWithinAt)

@[simp] lemma next_apply (x₀ : E) (α : Curve E) (t : Icc (0 : ℝ) 1) :
    next hf x₀ α t = ODE.picard f 0 x₀ (extend α) t := rfl

variable {K : ℝ≥0} (hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith K (f t))

include hL

lemma dist_comp_iterate_next_le (x₀ : E) (n : ℕ) (t : Icc (0 : ℝ) 1)
    {α β : Curve E}
    (h : dist ((next hf x₀)^[n] α t) ((next hf x₀)^[n] β t) ≤
      (K * |t.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf x₀)^[n] α t)) (f t ((next hf x₀)^[n] β t)) ≤
      K ^ (n + 1) * |t.1| ^ n / n ! * dist α β := by
  calc
    _ ≤ K * dist ((next hf x₀)^[n] α t) ((next hf x₀)^[n] β t) :=
      (hL t.1 t.2).dist_le_mul _ _
    _ ≤ K ^ (n + 1) * |t.1| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

lemma dist_iterate_next_apply_le (x₀ : E) (α β : Curve E) (n : ℕ)
    (t : Icc (0 : ℝ) 1) :
    dist ((next hf x₀)^[n] α t) ((next hf x₀)^[n] β t) ≤
      (K * |t.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp hf _ t)
        (intervalIntegrable_comp hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc (0 : ℝ) t.1,
          K ^ (n + 1) * |τ - 0| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro t' ht'
        have ht' : t' ∈ Icc (0 : ℝ) 1 :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc (by simp) t.2) ht'
        rw [← dist_eq_norm, extend_of_mem _ ht', extend_of_mem _ ht', sub_zero]
        exact dist_comp_iterate_next_le hf hL x₀ n ⟨t', ht'⟩ (hn _)
      _ ≤ (K * |t.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow,
          sub_zero]

lemma dist_iterate_next_le (x₀ : E) (α β : Curve E) (n : ℕ) :
    dist ((next hf x₀)^[n] α) ((next hf x₀)^[n] β) ≤
      (K : ℝ) ^ n / n ! * dist α β := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply le_trans (dist_iterate_next_apply_le hf hL x₀ α β n t)
  gcongr
  calc
    (K : ℝ) * |t.1| ≤ K * 1 := by gcongr; exact (abs_le.mpr ⟨by linarith [t.2.1], t.2.2⟩)
    _ = K := mul_one _

theorem exists_fixedPoint (x₀ : E) : ∃ α : Curve E, IsFixedPt (next hf x₀) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hc : ContractingWith ⟨(K : ℝ) ^ n / n !, by positivity⟩ ((next hf x₀)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul (fun α β => dist_iterate_next_le hf hL x₀ α β n)⟩
  exact ⟨_, hc.isFixedPt_fixedPoint_iterate⟩

end PropagatorConstruction

/-- A continuous vector field uniformly globally Lipschitz in the state has
a solution on the entire unit interval. -/
theorem exists_solution_unitInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {K : ℝ≥0}
    (hf : ContinuousOn (uncurry f) (Icc (0 : ℝ) 1 ×ˢ (univ : Set E)))
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith K (f t)) (x₀ : E) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt α (f t (α t)) (Icc (0 : ℝ) 1) t := by
  obtain ⟨α, hα⟩ := PropagatorConstruction.exists_fixedPoint hf hL x₀
  refine ⟨PropagatorConstruction.extend α, ?_, ?_⟩
  · rw [PropagatorConstruction.extend_of_mem _ (by simp), ← hα]
    simp [PropagatorConstruction.next_apply]
  · intro t ht
    apply (PropagatorConstruction.picard_deriv hf x₀ α ht).congr_of_mem _ ht
    intro s hs
    rw [PropagatorConstruction.extend_of_mem _ hs]
    nth_rw 1 [← hα]
    rfl

/-- A continuous coefficient in a complete real normed algebra generates an
evolution from every initial value on the entire unit interval. Compactness
provides the coefficient bound; there is no smallness condition. -/
theorem exists_mul_evolution_unitInterval
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G : ℝ → A} (hG : ContinuousOn G (Icc (0 : ℝ) 1)) (u₀ : A) :
    ∃ U : ℝ → A, U 0 = u₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U (G t * U t) (Icc (0 : ℝ) 1) t := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hMnonneg : 0 ≤ M := (norm_nonneg (G 0)).trans (hM 0 (by simp))
  apply exists_solution_unitInterval (K := ⟨M, hMnonneg⟩)
  · exact (hG.comp continuousOn_fst (fun _ hp => hp.1)).mul continuousOn_snd
  · intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← mul_sub, NNReal.coe_mk]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))

/-- The normalized propagator exists for every continuous algebra-valued
coefficient. This theorem supplies evolution, without a unitary assertion. -/
theorem exists_propagator_unitInterval
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G : ℝ → A} (hG : ContinuousOn G (Icc (0 : ℝ) 1)) :
    ∃ U : ℝ → A, U 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U (G t * U t) (Icc (0 : ℝ) 1) t :=
  exists_mul_evolution_unitInterval hG 1

end Adiabatic
