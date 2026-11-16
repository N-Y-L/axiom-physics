import Adiabatic.Unbounded.FrozenApproximation
import Adiabatic.Unbounded.HilbertGraphConvergence

/-!
# Graph estimates for limits of frozen evolutions

The sharp two-time shifted graph bound survives strong physical convergence.
It then supplies strong continuity of the limiting domain lift, completing
the domain-continuity step in the construction of a nonautonomous propagator.
-/

namespace Adiabatic.Unbounded

open Set Filter
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace CommonDomain

/-- Variable graph upper bounds pass to physical limits with their exact
limiting constant, tested on the dense self-adjoint domain. -/
theorem norm_shift_le_of_tendsto_inclusion_of_bound_tendsto
    (domain : CommonDomain D E) (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)
    {ι : Type*} {l : Filter ι} [l.NeBot] (x : ι → D) (y : D) (w : ℂ)
    (b : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hv : Tendsto (fun n => domain.inclusion (x n)) l (𝓝 (domain.inclusion y)))
    (hb : Tendsto b l (𝓝 M))
    (hbound : ∀ᶠ n in l, ‖domain.shift H w (x n)‖ ≤ b n) :
    ‖domain.shift H w y‖ ≤ M := by
  apply domain.norm_le_of_inner_bound_on_domain _ hM
  intro a
  have hi : Tendsto (fun n => inner ℂ (domain.shift H w (x n)) (domain.inclusion a))
      l (𝓝 (inner ℂ (domain.shift H w y) (domain.inclusion a))) := by
    simpa only [shift_apply, inner_sub_left, inner_smul_left, domain.inner_map H hH] using
      (hv.inner (tendsto_const_nhds (x := H a))).sub
        ((hv.inner (tendsto_const_nhds (x := domain.inclusion a))).const_mul (star w))
  apply le_of_tendsto_of_tendsto hi.norm (hb.mul_const ‖domain.inclusion a‖)
  filter_upwards [hbound] with n hn
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end CommonDomain

variable [CompleteSpace D] {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {z : ℂ}

namespace FrozenApproximation

variable (A : FrozenApproximation domain H z)

omit [CompleteSpace D] in
/-- Strong limits of the frozen forward and inverse evolutions inherit
the sharp shifted graph estimate with no remaining mesh error. -/
theorem norm_shift_limit_transition_le
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (U : ℝ → E →L[ℂ] E) (V W : ℝ → D →L[ℂ] D)
    (hpres : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, U t (domain.inclusion x) = domain.inclusion (V t x))
    (hinvpres : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      star (U t) (domain.inclusion x) = domain.inclusion (W t x))
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (A.family n).evolution t x) atTop (𝓝 (U t x)))
    (hlimadj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => star ((A.family n).evolution t) x) atTop (𝓝 (star (U t) x)))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    ‖domain.shift (H t) Complex.I (V t (W s x))‖ ≤
      Real.exp (A.graph_constant * |t - s|) * ‖domain.shift (H s) Complex.I x‖ := by
  let y : ℕ → D := fun n => (A.family n).lift t ((A.family n).inverseLift s x)
  let b : ℕ → ℝ := fun n => Real.exp (A.graph_constant * (|t - s| + 2 * gridMesh n)) *
    ‖domain.shift (H s) Complex.I x‖
  have hunit : ∀ᶠ n in atTop, ‖(A.family n).evolution t‖ ≤ 1 := by
    apply Eventually.of_forall
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary ((A.family n).isUnitary t)]
  have hy : Tendsto (fun n => domain.inclusion (y n)) atTop (𝓝 (domain.inclusion (V t (W s x)))) := by
    have hv := tendsto_apply_of_strong hunit (hlim t ht (star (U s) (domain.inclusion x)))
      (hlimadj s hs (domain.inclusion x))
    simpa only [y, (A.family _).inverse_preserves_domain, (A.family _).preserves_domain,
      hinvpres s hs, hpres t ht] using hv
  have hb : Tendsto b atTop
      (𝓝 (Real.exp (A.graph_constant * |t - s|) * ‖domain.shift (H s) Complex.I x‖)) := by
    have hc : Continuous (fun r : ℝ => Real.exp (A.graph_constant * (|t - s| + 2 * r)) *
        ‖domain.shift (H s) Complex.I x‖) := by fun_prop
    simpa only [Function.comp_def, b, mul_zero, add_zero] using (hc.tendsto 0).comp tendsto_gridMesh
  apply domain.norm_shift_le_of_tendsto_inclusion_of_bound_tendsto (H t) (hH t ht)
    y (V t (W s x)) Complex.I b (by positivity) hy hb
  apply Eventually.of_forall
  intro n
  exact (A.family n).norm_shift_transition_le A.graph_constant A.graph_constant_nonneg
    A.graph_change hs ht x

/-- The domain lift of the strong physical limit is strongly
continuous, using the graph estimate derived from the frozen evolutions. -/
theorem continuousOn_limit_lift
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (U : ℝ → E →L[ℂ] E) (V W : ℝ → D →L[ℂ] D)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary (E →L[ℂ] E))
    (hpres : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, U t (domain.inclusion x) = domain.inclusion (V t x))
    (hinvpres : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      star (U t) (domain.inclusion x) = domain.inclusion (W t x))
    (hc : ∀ x : E, ContinuousOn (fun t => U t x) (Icc (0 : ℝ) 1))
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (A.family n).evolution t x) atTop (𝓝 (U t x)))
    (hlimadj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => star ((A.family n).evolution t) x) atTop (𝓝 (star (U t) x)))
    (x : D) : ContinuousOn (fun t => V t x) (Icc (0 : ℝ) 1) := by
  apply domain.continuousOn_lift_of_graph_transition_bound H hH U V W hpres _ hc
    A.graph_constant A.graph_constant_nonneg A.graph_change _ x
  · intro t ht y
    apply domain.injective
    rw [← hinvpres t ht, ← hpres t ht]
    exact congrArg (fun B : E →L[ℂ] E => B (domain.inclusion y))
      (Unitary.star_mul_self_of_mem (hU t ht))
  · intro s hs t ht y
    exact A.norm_shift_limit_transition_le hH U V W hpres hinvpres hlim hlimadj hs ht y

end FrozenApproximation
end Adiabatic.Unbounded
