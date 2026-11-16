import Adiabatic.Unbounded.NonautonomousDomain

/-!
# Strong convergence in the common domain

Physical convergence and a sharp upper bound on shifted graph norms imply
strong convergence in the Banach common domain. The Hilbert space step uses
weak convergence and the norm identity, without compactness assumptions.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

open Filter
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (domain : CommonDomain D E)

/-- Uniformly bounded vectors converging weakly on the dense domain converge
weakly against every physical vector. -/
theorem tendsto_inner_of_bounded_on_domain
    {ι : Type*} {l : Filter ι} (f : ι → E) (v : E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᶠ n in l, ‖f n‖ ≤ M)
    (hweak : ∀ x : D, Tendsto (fun n => inner ℂ (f n) (domain.inclusion x)) l
      (𝓝 (inner ℂ v (domain.inclusion x)))) (y : E) :
    Tendsto (fun n => inner ℂ (f n) y) l (𝓝 (inner ℂ v y)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K := M + ‖v‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨a, ha⟩ := domain.dense.exists_dist_lt y (show 0 < ε / (4 * K) by positivity)
  have hi := Metric.tendsto_nhds.mp (hweak a) (ε / 2) (by positivity)
  filter_upwards [hbound, hi] with n hn hi
  rw [dist_eq_norm] at ha hi ⊢
  have heq : inner ℂ (f n) y - inner ℂ v y =
      inner ℂ (f n) (y - domain.inclusion a) +
        (inner ℂ (f n) (domain.inclusion a) - inner ℂ v (domain.inclusion a)) +
          inner ℂ v (domain.inclusion a - y) := by
    simp only [inner_sub_right]
    ring
  rw [heq]
  have hfirst : ‖inner ℂ (f n) (y - domain.inclusion a)‖ ≤
      M * ‖y - domain.inclusion a‖ := (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hlast : ‖inner ℂ v (domain.inclusion a - y)‖ ≤
      ‖v‖ * ‖y - domain.inclusion a‖ := by
    simpa only [norm_sub_rev] using norm_inner_le_norm v (domain.inclusion a - y)
  have hsmall : (M + ‖v‖) * ‖y - domain.inclusion a‖ < ε / 4 := by
    calc
      _ ≤ K * ‖y - domain.inclusion a‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [K]
        linarith
      _ < K * (ε / (4 * K)) := mul_lt_mul_of_pos_left ha hK
      _ = ε / 4 := by field_simp
  have htri : ‖inner ℂ (f n) (y - domain.inclusion a) +
        (inner ℂ (f n) (domain.inclusion a) - inner ℂ v (domain.inclusion a)) +
          inner ℂ v (domain.inclusion a - y)‖ ≤
      ‖inner ℂ (f n) (y - domain.inclusion a)‖ +
        ‖inner ℂ (f n) (domain.inclusion a) - inner ℂ v (domain.inclusion a)‖ +
          ‖inner ℂ v (domain.inclusion a - y)‖ := norm_add₃_le
  nlinarith

/-- Weak convergence and an asymptotically sharp upper bound on norms give
strong convergence in a Hilbert space. -/
theorem tendsto_of_inner_of_norm_upper
    {ι : Type*} {l : Filter ι} (f : ι → E) (v : E) (b : ι → ℝ)
    (hb : Tendsto b l (𝓝 ‖v‖)) (hbound : ∀ᶠ n in l, ‖f n‖ ≤ b n)
    (hweak : ∀ x : D, Tendsto (fun n => inner ℂ (f n) (domain.inclusion x)) l
      (𝓝 (inner ℂ v (domain.inclusion x)))) : Tendsto f l (𝓝 v) := by
  have hbounded : ∀ᶠ n in l, ‖f n‖ ≤ ‖v‖ + 1 := by
    filter_upwards [hbound, hb.eventually_le_const (by linarith : ‖v‖ < ‖v‖ + 1)] with n hn hb
    exact hn.trans hb
  have hi := domain.tendsto_inner_of_bounded_on_domain f v (by positivity : 0 ≤ ‖v‖ + 1)
    hbounded hweak v
  have hire := (Complex.continuous_re.tendsto (inner ℂ v v)).comp hi
  have hself : (inner ℂ v v).re = ‖v‖^2 := @inner_self_eq_norm_sq ℂ E _ _ _ v
  have hupper : Tendsto (fun n => (b n)^2 - 2 * (inner ℂ (f n) v).re + ‖v‖^2) l (𝓝 0) := by
    have hlim := ((hb.pow 2).sub (hire.const_mul 2)).add_const (‖v‖^2)
    rw [hself] at hlim
    have hz : ‖v‖^2 - 2 * ‖v‖^2 + ‖v‖^2 = 0 := by ring
    rwa [hz] at hlim
  have hsq : Tendsto (fun n => ‖f n - v‖^2) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) _ hupper
    filter_upwards [hbound] with n hn
    rw [@norm_sub_sq ℂ E _ _ _ (f n) v]
    change ‖f n‖^2 - 2 * (inner ℂ (f n) v).re + ‖v‖^2 ≤
      (b n)^2 - 2 * (inner ℂ (f n) v).re + ‖v‖^2
    linarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

variable [CompleteSpace D] [CompleteSpace E]

/-- Physical convergence and sharp shifted graph norm bounds imply strong
convergence in the full common Banach domain. -/
theorem tendsto_domain_of_tendsto_inclusion_of_shift_norm_upper
    (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)
    {ι : Type*} {l : Filter ι} (x : ι → D) (y : D) (b : ι → ℝ)
    (hv : Tendsto (fun n => domain.inclusion (x n)) l (𝓝 (domain.inclusion y)))
    (hb : Tendsto b l (𝓝 ‖domain.shift H Complex.I y‖))
    (hbound : ∀ᶠ n in l, ‖domain.shift H Complex.I (x n)‖ ≤ b n) :
    Tendsto x l (𝓝 y) := by
  have hgraph : Tendsto (fun n => domain.shift H Complex.I (x n)) l
      (𝓝 (domain.shift H Complex.I y)) := by
    apply domain.tendsto_of_inner_of_norm_upper _ _ b hb hbound
    intro a
    simpa only [shift_apply, inner_sub_left, inner_smul_left, domain.inner_map H hH] using
      (hv.inner (tendsto_const_nhds (x := H a))).sub
        ((hv.inner (tendsto_const_nhds (x := domain.inclusion a))).const_mul (star Complex.I))
  have hp := domain.mem_resolventSet_of_im_ne_zero H hH Complex.I (by simp)
  have hr := (domain.inverseShift H Complex.I).continuous.tendsto (domain.shift H Complex.I y)
  simpa only [Function.comp_def, domain.inverseShift_shift H Complex.I hp] using hr.comp hgraph

/-- Sharp two-time graph bounds upgrade a physically continuous evolution
to a strongly continuous evolution on its common Banach domain. -/
theorem continuousOn_lift_of_graph_transition_bound
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Set.Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (U : ℝ → E →L[ℂ] E) (V W : ℝ → D →L[ℂ] D)
    (hpres : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, U t (domain.inclusion x) = domain.inclusion (V t x))
    (hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, W t (V t x) = x)
    (hc : ∀ x : E, ContinuousOn (fun t => U t x) (Set.Icc (0 : ℝ) 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchange : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I x‖ ≤
        (1 + K * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (htransition : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : D,
      ‖domain.shift (H t) Complex.I (V t (W s x))‖ ≤
        Real.exp (K * |t - s|) * ‖domain.shift (H s) Complex.I x‖)
    (x : D) : ContinuousOn (fun t => V t x) (Set.Icc (0 : ℝ) 1) := by
  intro s hs
  have hv : Tendsto (fun t => domain.inclusion (V t x)) (𝓝[Set.Icc (0 : ℝ) 1] s)
      (𝓝 (domain.inclusion (V s x))) := by
    have hu := hc (domain.inclusion x) s hs
    rw [ContinuousWithinAt, hpres s hs x] at hu
    apply (tendsto_congr' ?_).mp hu
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpres t ht x
  let b : ℝ → ℝ := fun t =>
    (1 + K * |t - s|) * Real.exp (K * |t - s|) * ‖domain.shift (H s) Complex.I (V s x)‖
  have hb : Tendsto b (𝓝[Set.Icc (0 : ℝ) 1] s)
      (𝓝 ‖domain.shift (H s) Complex.I (V s x)‖) := by
    have hcont : Continuous b := by dsimp [b]; fun_prop
    simpa only [ContinuousWithinAt, b, sub_self, abs_zero, mul_zero, add_zero, Real.exp_zero, mul_one, one_mul] using
      hcont.continuousWithinAt (s := Set.Icc (0 : ℝ) 1) (x := s)
  apply domain.tendsto_domain_of_tendsto_inclusion_of_shift_norm_upper (H s) (hH s hs)
    (fun t => V t x) (V s x) b hv hb
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htbound := htransition s hs t ht (V s x)
  rw [hinv s hs x] at htbound
  calc
    _ ≤ (1 + K * |s - t|) * ‖domain.shift (H t) Complex.I (V t x)‖ :=
      hchange t ht s hs _
    _ ≤ (1 + K * |s - t|) *
        (Real.exp (K * |t - s|) * ‖domain.shift (H s) Complex.I (V s x)‖) :=
      mul_le_mul_of_nonneg_left htbound (by positivity)
    _ = b t := by rw [abs_sub_comm]; dsimp [b]; ring

end Adiabatic.Unbounded.CommonDomain
