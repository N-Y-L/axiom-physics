import Adiabatic.Unbounded.Autonomous
import Adiabatic.Unbounded.NonautonomousDomain
import Adiabatic.Unbounded.RightPropagator
import Adiabatic.Unbounded.GraphLimit

/-!
# Strong evolution for a C¹ self-adjoint common-domain Hamiltonian

Finite products of the constructed autonomous groups approximate the
Hamiltonian uniformly in the domain-to-physical operator norm. Uniform
domain bounds make both the forward and adjoint products strongly Cauchy,
so their limits form a unitary evolution. Maximal self-adjointness
recovers domain invariance, and sharp shifted graph estimates give strong
continuity in the common Banach domain.

A local comparison with the frozen autonomous group has quadratic error
in the time increment. This proves the time-dependent strong Schrödinger
equation, including the derivatives within the interval at both endpoints.
The final theorem constructs a `StrongPropagator` from C¹ regularity and
self-adjointness.
-/

namespace Adiabatic.Unbounded

open Set Filter
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A uniform comparison bound for two right strong approximations. -/
theorem norm_right_approximation_sub_restricted_le
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (U : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(U n).lift t‖ ≤ B)
    (m n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖((U m).evolution t - (U n).evolution t).comp domain.inclusion‖ ≤
      (‖z‖ * B) * (a m + a n) := by
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 (by simp))
  have hanonneg (k : ℕ) : 0 ≤ a k := (norm_nonneg _).trans (happrox k 0 (by simp))
  have hdiff : ∀ s ∈ Ico (0 : ℝ) 1, ‖Hn m s - Hn n s‖ ≤ a m + a n := by
    intro s hs
    have h := norm_sub_le (Hn m s - H s) (Hn n s - H s)
    simpa only [sub_sub_sub_cancel_right] using h.trans (add_le_add (happrox m s hs) (happrox n s hs))
  apply (right_strong_propagator_perturbation (U m) (U n) hdiff (hB m) ht).trans
  calc
    t * ‖z‖ * (a m + a n) * B ≤ 1 * ‖z‖ * (a m + a n) * B := by
      gcongr
      · exact add_nonneg (hanonneg m) (hanonneg n)
      · exact ht.2
    _ = (‖z‖ * B) * (a m + a n) := by ring

/-- Uniform coefficient approximation and domain bounds make the physical
evolutions Cauchy in the operator norm from the common domain to the
physical space. -/
theorem cauchySeq_restricted_right_evolution
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (U : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(U n).lift t‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    CauchySeq (fun n => ((U n).evolution t).comp domain.inclusion) := by
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0 0 (by simp))
  have hanonneg (n : ℕ) : 0 ≤ a n := (norm_nonneg _).trans (happrox n 0 (by simp))
  have hdiff (m n : ℕ) : ∀ s ∈ Ico (0 : ℝ) 1, ‖Hn m s - Hn n s‖ ≤ a m + a n := by
    intro s hs
    have h := norm_sub_le (Hn m s - H s) (Hn n s - H s)
    simpa only [sub_sub_sub_cancel_right] using h.trans (add_le_add (happrox m s hs) (happrox n s hs))
  have hdist (m n : ℕ) :
      dist (((U m).evolution t).comp domain.inclusion) (((U n).evolution t).comp domain.inclusion) ≤
        (‖z‖ * B) * (a m + a n) := by
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
    have hp := right_strong_propagator_perturbation (U m) (U n) (hdiff m n) (hB m) ht
    apply hp.trans
    calc
      t * ‖z‖ * (a m + a n) * B ≤ 1 * ‖z‖ * (a m + a n) * B := by
        gcongr
        · exact add_nonneg (hanonneg m) (hanonneg n)
        · exact ht.2
      _ = (‖z‖ * B) * (a m + a n) := by ring
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hpos : 0 < 2 * (‖z‖ * B + 1) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ha.eventually (gt_mem_nhds (show 0 < ε / (2 * (‖z‖ * B + 1)) by positivity)))
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hm' := (lt_div_iff₀ hpos).mp (hN m hm)
  have hn' := (lt_div_iff₀ hpos).mp (hN n hn)
  have hp := hdist m n
  nlinarith [hanonneg m, hanonneg n, mul_nonneg (norm_nonneg z) hBnonneg]

/-- Cauchy convergence on the common domain extends strongly to all
physical vectors because every approximating evolution is unitary. -/
theorem cauchySeq_right_evolution_apply
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (U : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(U n).lift t‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : E) :
    CauchySeq (fun n => (U n).evolution t x) := by
  apply cauchySeq_apply_of_dense_isometries domain.dense
    (fun n y => ContinuousLinearMap.norm_map_of_mem_unitary ((U n).isUnitary t ht) y) ?_ x
  intro y
  have hc := cauchySeq_restricted_right_evolution U ha happrox hB ht
  exact ((ContinuousLinearMap.apply ℂ E y).uniformContinuous.comp_cauchySeq hc)

/-- Uniform inverse-domain bounds transfer Cauchy convergence of restricted
unitaries to their restricted adjoints. -/
theorem cauchySeq_adjoint_restricted_of_cauchy
    (j : D →L[ℂ] E) (A : ℕ → E →L[ℂ] E) (V : ℕ → D →L[ℂ] D)
    (hA : ∀ n, A n ∈ unitary (E →L[ℂ] E))
    (hV : ∀ n x, star (A n) (j x) = j (V n x)) {B : ℝ}
    (hB : ∀ n, ‖V n‖ ≤ B) (hc : CauchySeq (fun n => (A n).comp j)) :
    CauchySeq (fun n => (star (A n)).comp j) := by
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hleft (n : ℕ) (x : E) : star (A n) (A n x) = x :=
    congrArg (fun T : E →L[ℂ] E => T x) (Unitary.star_mul_self_of_mem (hA n))
  have hright (n : ℕ) (x : E) : A n (star (A n) x) = x :=
    congrArg (fun T : E →L[ℂ] E => T x) (Unitary.mul_star_self_of_mem (hA n))
  have hnorm (m n : ℕ) : ‖(star (A m) - star (A n)).comp j‖ ≤ ‖(A n - A m).comp j‖ * B := by
    have heq : (star (A m) - star (A n)).comp j =
        (star (A m)).comp (((A n - A m).comp j).comp (V n)) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
      rw [← hV n x, map_sub, hright n, hleft m]
    rw [heq]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hBnonneg)
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (hA m))]
    calc
      ‖((A n - A m).comp j) (V n x)‖ ≤ ‖(A n - A m).comp j‖ * ‖V n x‖ :=
        ((A n - A m).comp j).le_opNorm _
      _ ≤ ‖(A n - A m).comp j‖ * (B * ‖x‖) := by
        gcongr
        exact ((V n).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg x))
      _ = (‖(A n - A m).comp j‖ * B) * ‖x‖ := by ring
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hpos : 0 < B + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε / (B + 1)) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hh := hN n hn m hm
  rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp] at hh ⊢
  have h := (lt_div_iff₀ hpos).mp hh
  nlinarith [hnorm m n, norm_nonneg ((A n - A m).comp j)]

/-- Cauchy restricted unitary operators with controlled inverse-domain
maps have a unitary strong limit on the physical Hilbert space. -/
theorem exists_unitary_strong_limit_of_restricted_cauchy
    (domain : CommonDomain D E) (A : ℕ → E →L[ℂ] E) (V : ℕ → D →L[ℂ] D)
    (hA : ∀ n, A n ∈ unitary (E →L[ℂ] E))
    (hV : ∀ n x, star (A n) (domain.inclusion x) = domain.inclusion (V n x)) {B : ℝ}
    (hB : ∀ n, ‖V n‖ ≤ B) (hc : CauchySeq (fun n => (A n).comp domain.inclusion)) :
    ∃ W : E →L[ℂ] E, W ∈ unitary (E →L[ℂ] E) ∧
      (∀ x, Tendsto (fun n => A n x) atTop (𝓝 (W x))) ∧
      ∀ x, Tendsto (fun n => star (A n) x) atTop (𝓝 (star W x)) := by
  have hca := cauchySeq_adjoint_restricted_of_cauchy domain.inclusion A V hA hV hB hc
  have hex (T : ℕ → E →L[ℂ] E) (hT : ∀ n, T n ∈ unitary (E →L[ℂ] E))
      (hcT : CauchySeq (fun n => (T n).comp domain.inclusion)) :
      ∃ W : E →L[ℂ] E, ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (W x)) := by
    have hcx (x : E) : CauchySeq (fun n => T n x) := by
      apply cauchySeq_apply_of_dense_isometries domain.dense
        (fun n y => ContinuousLinearMap.norm_map_of_mem_unitary (hT n) y) ?_ x
      intro y
      exact (ContinuousLinearMap.apply ℂ E y).uniformContinuous.comp_cauchySeq hcT
    choose w hw using (fun x => cauchySeq_tendsto_of_complete (hcx x))
    have hb : Bornology.IsBounded (range T) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨1, ?_⟩
      rintro _ ⟨n, rfl⟩
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary (hT n)]
    exact ⟨ContinuousLinearMap.ofTendstoOfBoundedRange w T (tendsto_pi_nhds.mpr hw) hb, hw⟩
  obtain ⟨W, hW⟩ := hex A hA hc
  obtain ⟨Z, hZ⟩ := hex (fun n => star (A n)) (fun n => Unitary.star_mem (hA n)) hca
  have hnorm (x : E) : ‖W x‖ = ‖x‖ := by
    apply tendsto_nhds_unique (hW x).norm
    simpa only [ContinuousLinearMap.norm_map_of_mem_unitary (hA _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))
  have hright : W * Z = 1 := by
    ext x
    have hb : ∀ᶠ n in atTop, ‖A n‖ ≤ 1 := Eventually.of_forall (fun n => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro y
      rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary (hA n)])
    have hp := tendsto_apply_of_strong hb (hW (Z x)) (hZ x)
    apply tendsto_nhds_unique hp
    have heq (n : ℕ) : A n (star (A n) x) = x :=
      congrArg (fun T : E →L[ℂ] E => T x) (Unitary.mul_star_self_of_mem (hA n))
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  have hleft : star W * W = 1 := W.norm_map_iff_adjoint_comp_self.mp hnorm
  have hZeq : Z = star W := by
    calc
      Z = (star W * W) * Z := by rw [hleft, one_mul]
      _ = star W := by rw [mul_assoc, hright, mul_one]
  refine ⟨W, Unitary.mem_iff.mpr ⟨hleft, ?_⟩, hW, ?_⟩
  · simpa only [hZeq] using hright
  · simpa only [hZeq] using hZ

/-- Right strong approximations with vanishing coefficient error
and uniform forward and inverse domain bounds construct normalized unitary
physical limits. Both the propagators and their adjoints converge strongly. -/
theorem exists_unitary_limit_of_right_approximations
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B C : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (hC : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).inverseLift t‖ ≤ C) :
    ∃ U : ℝ → E →L[ℂ] E, U 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary (E →L[ℂ] E)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x))) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        Tendsto (fun n => star ((V n).evolution t) x) atTop (𝓝 (star (U t) x)) := by
  have hex (t : Icc (0 : ℝ) 1) : ∃ W : E →L[ℂ] E,
      W ∈ unitary (E →L[ℂ] E) ∧
        (∀ x, Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (W x))) ∧
        ∀ x, Tendsto (fun n => star ((V n).evolution t) x) atTop (𝓝 (star W x)) :=
    exists_unitary_strong_limit_of_restricted_cauchy domain
      (fun n => (V n).evolution t) (fun n => (V n).inverseLift t)
      (fun n => (V n).isUnitary t t.2) (fun n => (V n).inverse_preserves_domain t t.2)
      (fun n => hC n t t.2) (cauchySeq_restricted_right_evolution V ha happrox hB t.2)
  choose W hW hforw hback using hex
  let U : ℝ → E →L[ℂ] E := fun t => W (projIcc 0 1 zero_le_one t)
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x)) := by
    intro t ht x
    simpa only [U, projIcc_of_mem _ ht] using hforw ⟨t, ht⟩ x
  refine ⟨U, ?_, ?_, hf, ?_⟩
  · ext x
    apply tendsto_nhds_unique (hf 0 (by simp) x)
    simpa only [RightStrongPropagator.initial, ContinuousLinearMap.one_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  · intro t ht
    simpa only [U, projIcc_of_mem _ ht] using hW ⟨t, ht⟩
  · intro t ht x
    simpa only [U, projIcc_of_mem _ ht] using hback ⟨t, ht⟩ x

/-- The quantitative approximation bound passes to a strong physical
limit on every vector in the common domain. -/
theorem norm_right_approximation_sub_limit_apply_le
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (U : ℝ → E →L[ℂ] E)
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x)))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    dist ((V n).evolution t (domain.inclusion x)) (U t (domain.inclusion x)) ≤
      (‖z‖ * B) * a n * ‖x‖ := by
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds.dist (hlim t ht (domain.inclusion x)))
    (show Tendsto (fun m => (‖z‖ * B) * (a n + a m) * ‖x‖) atTop
      (𝓝 ((‖z‖ * B) * a n * ‖x‖)) from by
        simpa using ((tendsto_const_nhds.add ha).const_mul (‖z‖ * B)).mul_const ‖x‖)
  apply Eventually.of_forall
  intro m
  dsimp only
  rw [dist_eq_norm]
  have hb := norm_right_approximation_sub_restricted_le V happrox hB n m ht
  exact (((V n).evolution t - (V m).evolution t).comp domain.inclusion).le_of_opNorm_le hb x

/-- The strong physical convergence is uniform on the full time interval,
including for vectors outside the Hamiltonian domain. -/
theorem right_approximation_tendstoUniformlyOn
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (U : ℝ → E →L[ℂ] E)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary (E →L[ℂ] E))
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x))) (x : E) :
    TendstoUniformlyOn (fun n t => (V n).evolution t x) (fun t => U t x) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := domain.dense.exists_dist_lt x (show 0 < ε / 3 by positivity)
  have herr : Tendsto (fun n => (‖z‖ * B) * a n * ‖y‖) atTop (𝓝 0) := by
    simpa using (ha.const_mul (‖z‖ * B)).mul_const ‖y‖
  filter_upwards [herr.eventually (gt_mem_nhds (show 0 < ε / 3 by positivity))] with n hn t ht
  have hmid := norm_right_approximation_sub_limit_apply_le V ha happrox hB U hlim n ht y
  have hd₁ : dist ((V n).evolution t x) ((V n).evolution t (domain.inclusion y)) =
      dist x (domain.inclusion y) := by
    simp only [dist_eq_norm, ← map_sub,
      ContinuousLinearMap.norm_map_of_mem_unitary ((V n).isUnitary t ht)]
  have hd₂ : dist (U t (domain.inclusion y)) (U t x) = dist x (domain.inclusion y) := by
    rw [dist_comm]
    simp only [dist_eq_norm, ← map_sub, ContinuousLinearMap.norm_map_of_mem_unitary (hU t ht)]
  have htri := dist_triangle ((V n).evolution t x) ((V n).evolution t (domain.inclusion y)) (U t x)
  have htri₂ := dist_triangle ((V n).evolution t (domain.inclusion y)) (U t (domain.inclusion y)) (U t x)
  rw [hd₁] at htri
  rw [hd₂] at htri₂
  rw [dist_comm]
  linarith

/-- The unitary limit is strongly continuous as a uniform limit of the
constructed right strong approximations. -/
theorem continuousOn_right_approximation_limit
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (U : ℝ → E →L[ℂ] E)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary (E →L[ℂ] E))
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x))) (x : E) :
    ContinuousOn (fun t => U t x) (Icc (0 : ℝ) 1) :=
  (right_approximation_tendstoUniformlyOn V ha happrox hB U hU hlim x).continuousOn
    (Eventually.of_forall (fun n => (V n).strong_continuous x)).frequently

/-- Uniform domain bounds and strong physical convergence construct a
bounded linear map on the common domain for the limiting unitary. -/
theorem exists_limit_domain_lift [CompleteSpace D]
    (domain : CommonDomain D E) (H₀ : D →L[ℂ] E) (hH₀ : domain.IsSelfAdjoint H₀)
    (A : ℕ → E →L[ℂ] E) (L : ℕ → D →L[ℂ] D)
    (hL : ∀ n x, A n (domain.inclusion x) = domain.inclusion (L n x)) {B : ℝ}
    (hB : ∀ n, ‖L n‖ ≤ B) (U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E))
    (hlim : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (U x))) :
    ∃ V : D →L[ℂ] D, ∀ x, U (domain.inclusion x) = domain.inclusion (V x) := by
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hex (x : D) : ∃ y : D, domain.inclusion y = U (domain.inclusion x) ∧
      ‖H₀ y‖ ≤ ‖H₀‖ * B * ‖x‖ := by
    apply domain.exists_domain_vector_of_tendsto_of_bound H₀ hH₀ (l := atTop) (fun n => L n x)
      (U (domain.inclusion x)) (by positivity)
    · simpa only [← hL] using hlim (domain.inclusion x)
    · apply Eventually.of_forall
      intro n
      calc
        ‖H₀ (L n x)‖ ≤ ‖H₀‖ * ‖L n x‖ := H₀.le_opNorm _
        _ ≤ ‖H₀‖ * (B * ‖x‖) := by
          gcongr
          exact ((L n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg x))
        _ = ‖H₀‖ * B * ‖x‖ := by ring
  choose v hv hHv using hex
  let V₀ : D →ₗ[ℂ] D := {
    toFun := v
    map_add' := fun x y => domain.injective (by simp only [map_add, hv])
    map_smul' := fun c x => domain.injective (by simp only [map_smul, hv, RingHom.id_apply])
  }
  obtain ⟨C, hC, hgraph⟩ := domain.norm_le_graph H₀ hH₀
  have hnorm (x : D) : ‖V₀ x‖ ≤ C * (‖domain.inclusion‖ + ‖H₀‖ * B) * ‖x‖ := by
    calc
      ‖V₀ x‖ ≤ C * (‖domain.inclusion (v x)‖ + ‖H₀ (v x)‖) := hgraph (v x)
      _ ≤ C * (‖domain.inclusion‖ * ‖x‖ + ‖H₀‖ * B * ‖x‖) := by
        rw [hv, ContinuousLinearMap.norm_map_of_mem_unitary hU]
        gcongr
        · exact domain.inclusion.le_opNorm x
        · exact hHv x
      _ = C * (‖domain.inclusion‖ + ‖H₀‖ * B) * ‖x‖ := by ring
  exact ⟨V₀.mkContinuous (C * (‖domain.inclusion‖ + ‖H₀‖ * B)) hnorm, fun x => (hv x).symm⟩

/-- Compare a right strong evolution with an autonomous frozen group on
an arbitrary subinterval, without requiring equal initial values there. -/
theorem right_strong_frozen_comparison_of_le
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {H₀ : D →L[ℂ] E} {z : ℂ}
    (V : RightStrongPropagator domain H z) (F : domain.AutonomousGroup H₀ z)
    {a b ε B : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hε : 0 ≤ ε)
    (hH : ∀ t ∈ Ico a b, ‖H t - H₀‖ ≤ ε)
    (hB : ∀ t ∈ Icc a b, ‖V.lift t‖ ≤ B) (x : D) :
    ‖V.evolution b (domain.inclusion x) -
        F.evolution (b - a) (V.evolution a (domain.inclusion x))‖ ≤
      (b - a) * ‖z‖ * ε * B * ‖x‖ := by
  let f := fun t => F.evolution (-t) (V.evolution t (domain.inclusion x))
  have hfc : ContinuousOn f (Icc a b) := by
    intro t ht
    apply tendsto_apply_of_strong (M := 1)
    · exact Eventually.of_forall (fun u => F.norm_le_one (-u))
    · exact ((F.strong_continuous _).comp continuous_neg).continuousAt.continuousWithinAt
    · exact V.strong_continuous _ t ⟨ha.trans ht.1, ht.2.trans hb⟩ |>.mono (Icc_subset_Icc ha hb)
  have hf (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt f
        (z • F.evolution (-t) ((H t - H₀) (V.lift t x))) (Ici t) t := by
    have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ha.trans ht.1, ht.2.trans_le hb⟩
    have hfixed := (F.inverse_derivative (V.lift t x) t).hasDerivWithinAt (s := Ici t)
    rw [← V.preserves_domain t ⟨ht'.1, ht'.2.le⟩] at hfixed
    convert hasDerivWithinAt_apply_of_strong
      (A := fun u => F.evolution (-u)) (v := fun u => V.evolution u (domain.inclusion x))
      (M := 1) (Eventually.of_forall (fun u => F.norm_le_one (-u)))
      (((F.strong_continuous _).comp continuous_neg).continuousAt.continuousWithinAt)
      hfixed (V.strong_right_derivative x t ht') using 1
    simp only [map_smul, ContinuousLinearMap.sub_apply, map_sub, smul_sub]
    module
  have hnorm (t : ℝ) (ht : t ∈ Ico a b) :
      ‖z • F.evolution (-t) ((H t - H₀) (V.lift t x))‖ ≤ ‖z‖ * ε * B * ‖x‖ := by
    rw [norm_smul, ContinuousLinearMap.norm_map_of_mem_unitary (F.isUnitary (-t))]
    calc
      ‖z‖ * ‖(H t - H₀) (V.lift t x)‖ ≤ ‖z‖ * (‖H t - H₀‖ * ‖V.lift t x‖) := by
        gcongr; exact (H t - H₀).le_opNorm _
      _ ≤ ‖z‖ * (ε * (B * ‖x‖)) := by
        gcongr
        · exact hH t ht
        · exact ((V.lift t).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hB t ⟨ht.1, ht.2.le⟩) (norm_nonneg x))
      _ = ‖z‖ * ε * B * ‖x‖ := by ring
  have hmean := norm_image_sub_le_of_norm_deriv_right_le_segment hfc hf hnorm b ⟨hab, le_rfl⟩
  have hgroup : F.evolution (-b) * F.evolution (b - a) = F.evolution (-a) := by
    rw [← F.group_law]
    congr 1
    ring
  have heq : f b - f a = F.evolution (-b)
      (V.evolution b (domain.inclusion x) - F.evolution (b - a) (V.evolution a (domain.inclusion x))) := by
    dsimp [f]
    rw [map_sub]
    congr 1
    exact (congrArg (fun A : E →L[ℂ] E => A (V.evolution a (domain.inclusion x))) hgroup).symm
  rw [heq, ContinuousLinearMap.norm_map_of_mem_unitary (F.isUnitary (-b))] at hmean
  convert hmean using 1; ring

/-- The frozen comparison estimate holds in either direction in time. -/
theorem right_strong_frozen_comparison
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {H₀ : D →L[ℂ] E} {z : ℂ}
    (V : RightStrongPropagator domain H z) (F : domain.AutonomousGroup H₀ z)
    {a b ε B : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hε : 0 ≤ ε)
    (hH : ∀ t ∈ Ico (min a b) (max a b), ‖H t - H₀‖ ≤ ε)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖V.lift t‖ ≤ B) (x : D) :
    ‖V.evolution b (domain.inclusion x) -
        F.evolution (b - a) (V.evolution a (domain.inclusion x))‖ ≤
      |b - a| * ‖z‖ * ε * B * ‖x‖ := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      right_strong_frozen_comparison_of_le V F hab ha.1 hb.2 hε
        (by simpa only [min_eq_left hab, max_eq_right hab] using hH)
        (fun t ht => hB t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩) x
  · have hv := right_strong_frozen_comparison_of_le V F hba hb.1 ha.2 hε
        (by simpa only [min_eq_right hba, max_eq_left hba] using hH)
        (fun t ht => hB t ⟨hb.1.trans ht.1, ht.2.trans ha.2⟩) x
    have hgroup : F.evolution (b - a) * F.evolution (a - b) = 1 := by
      rw [← F.group_law, sub_add_sub_cancel, sub_self, F.initial]
    have heq : F.evolution (b - a)
        (V.evolution a (domain.inclusion x) -
          F.evolution (a - b) (V.evolution b (domain.inclusion x))) =
        F.evolution (b - a) (V.evolution a (domain.inclusion x)) -
          V.evolution b (domain.inclusion x) := by
      rw [map_sub]
      congr 1
      exact congrArg (fun A : E →L[ℂ] E => A (V.evolution b (domain.inclusion x))) hgroup
    have hn := ContinuousLinearMap.norm_map_of_mem_unitary (F.isUnitary (b - a))
      (V.evolution a (domain.inclusion x) -
        F.evolution (a - b) (V.evolution b (domain.inclusion x)))
    rw [heq, norm_sub_rev] at hn
    rw [hn, abs_of_nonpos (sub_nonpos.mpr hba)]
    convert hv using 1; ring

/-- A Lipschitz Hamiltonian leaves a quadratic error when the limiting
strong evolution is compared locally with its frozen autonomous group. -/
theorem norm_limit_sub_frozen_le
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B L : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖H s - H t‖ ≤ L * |s - t|)
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (U : ℝ → E →L[ℂ] E)
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (F : domain.AutonomousGroup (H t) z)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : D) :
    ‖U s (domain.inclusion x) - F.evolution (s - t) (U t (domain.inclusion x))‖ ≤
      (‖z‖ * L * B * ‖x‖) * |s - t| ^ 2 := by
  have hanonneg (n : ℕ) : 0 ≤ a n := (norm_nonneg _).trans (happrox n 0 (by simp))
  have hlocal (n : ℕ) :
      ‖(V n).evolution s (domain.inclusion x) -
        F.evolution (s - t) ((V n).evolution t (domain.inclusion x))‖ ≤
        |s - t| * ‖z‖ * (a n + L * |s - t|) * B * ‖x‖ := by
    apply right_strong_frozen_comparison (V n) F ht hs (add_nonneg (hanonneg n) (mul_nonneg hL (abs_nonneg _))) _ (hB n)
    intro u hu
    have hu' : u ∈ Ico (0 : ℝ) 1 :=
      ⟨(le_min ht.1 hs.1).trans hu.1, hu.2.trans_le (max_le ht.2 hs.2)⟩
    have hdist : |u - t| ≤ |s - t| := by
      rcases le_total t s with hts | hst
      · simp only [min_eq_left hts, max_eq_right hts] at hu
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1), abs_of_nonneg (sub_nonneg.mpr hts)]
        linarith [hu.2]
      · simp only [min_eq_right hst, max_eq_left hst] at hu
        rw [abs_of_nonpos (sub_nonpos.mpr hu.2.le), abs_of_nonpos (sub_nonpos.mpr hst)]
        linarith [hu.1]
    calc
      ‖Hn n u - H t‖ ≤ ‖Hn n u - H u‖ + ‖H u - H t‖ := by simpa only [dist_eq_norm] using dist_triangle (Hn n u) (H u) (H t)
      _ ≤ a n + L * |u - t| := add_le_add (happrox n u hu') (hLip u ⟨hu'.1, hu'.2.le⟩ t ht)
      _ ≤ a n + L * |s - t| := by gcongr
  have hleft := ((hlim s hs (domain.inclusion x)).sub
    ((F.evolution (s - t)).continuous.tendsto _ |>.comp (hlim t ht (domain.inclusion x)))).norm
  have hright : Tendsto (fun n => |s - t| * ‖z‖ * (a n + L * |s - t|) * B * ‖x‖)
      atTop (𝓝 ((‖z‖ * L * B * ‖x‖) * |s - t| ^ 2)) := by
    have heq : |s - t| * ‖z‖ * (0 + L * |s - t|) * B * ‖x‖ =
        (‖z‖ * L * B * ‖x‖) * |s - t| ^ 2 := by ring
    simpa only [heq] using
      (((ha.add_const (L * |s - t|)).const_mul (|s - t| * ‖z‖)).mul_const B).mul_const ‖x‖
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hlocal)

omit [CompleteSpace E] in
/-- A quadratic remainder preserves a derivative, including one-sided
endpoint derivatives on an arbitrary set. -/
theorem hasDerivWithinAt_of_quadratic_error
    {f g : ℝ → E} {v : E} {S : Set ℝ} {t C : ℝ}
    (hg : HasDerivWithinAt g v S t) (heq : f t = g t)
    (herror : ∀ s ∈ S, ‖f s - g s‖ ≤ C * |s - t| ^ 2) :
    HasDerivWithinAt f v S t := by
  have herr : HasDerivWithinAt (fun s => f s - g s) 0 S t := by
    rw [hasDerivWithinAt_iff_tendsto]
    simp only [heq, sub_self, smul_zero, sub_zero]
    have hlim : Tendsto (fun s : ℝ => C * |s - t|) (𝓝[S] t) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => C * |s - t|) := by fun_prop
      simpa only [ContinuousWithinAt, sub_self, abs_zero, mul_zero] using
        hc.continuousWithinAt (s := S) (x := t)
    apply squeeze_zero' (Eventually.of_forall fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    calc
      ‖s - t‖⁻¹ * ‖f s - g s‖ ≤ ‖s - t‖⁻¹ * (C * |s - t| ^ 2) :=
        mul_le_mul_of_nonneg_left (herror s hs) (inv_nonneg.mpr (norm_nonneg _))
      _ = C * |s - t| := by
        rw [Real.norm_eq_abs]
        by_cases hst : s - t = 0
        · simp [hst]
        · have hne : |s - t| ≠ 0 := abs_ne_zero.mpr hst
          field_simp
  have hsum : HasDerivWithinAt (fun s => g s + (f s - g s)) (v + 0) S t := hg.add herr
  convert hsum using 1
  · ext s
    module
  · simp

/-- The strong limit satisfies the time-dependent Schrödinger
equation on every common-domain vector. -/
theorem hasDerivWithinAt_right_approximation_limit [CompleteSpace D]
    {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {Hn : ℕ → ℝ → D →L[ℂ] E} {z : ℂ}
    (V : ∀ n, RightStrongPropagator domain (Hn n) z) {a : ℕ → ℝ} {B L : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖H s - H t‖ ≤ L * |s - t|)
    (happrox : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖Hn n t - H t‖ ≤ a n)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(V n).lift t‖ ≤ B)
    (U : ℝ → E →L[ℂ] E) (W : ℝ → D →L[ℂ] D)
    (hpres : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, U t (domain.inclusion x) = domain.inclusion (W t x))
    (hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      Tendsto (fun n => (V n).evolution t x) atTop (𝓝 (U t x)))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) (hz : star z = -z)
    (x : D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => U s (domain.inclusion x))
      (z • H t (W t x)) (Icc (0 : ℝ) 1) t := by
  obtain ⟨F⟩ := domain.exists_autonomousGroup (H t) (hH t ht) z hz
  have hzero (y : D) : F.lift 0 y = y := by
    apply domain.injective
    rw [← F.preserves_domain, F.initial, ContinuousLinearMap.one_apply]
  have hdf : HasDerivAt
      (fun s => F.evolution (s - t) (U t (domain.inclusion x))) (z • H t (W t x)) t := by
    rw [hpres t ht x]
    simpa only [Function.comp_def, sub_self, hzero, one_smul] using
      (F.strong_derivative (W t x) (t - t)).scomp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
  apply hasDerivWithinAt_of_quadratic_error hdf.hasDerivWithinAt
    (by rw [sub_self, F.initial, ContinuousLinearMap.one_apply])
  intro s hs
  exact norm_limit_sub_frozen_le V ha hL hLip happrox hB U hlim ht F hs x

/-- Every C¹ self-adjoint family on a fixed complete common domain has
a normalized unitary strong propagator. The domain is preserved in
both directions, and the evolution is strongly continuous in its Banach
norm. -/
theorem exists_nonautonomous_strongPropagator [CompleteSpace D]
    (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (z : ℂ) (hz : star z = -z) :
    Nonempty (StrongPropagator domain H (fun _ => 0) z) := by
  obtain ⟨A⟩ := exists_frozenApproximation domain H z hc hH hz
  let F : ∀ n, RightStrongPropagator domain (stepHamiltonian H n) z :=
    fun n => (A.family n).toRightStrongPropagator hH
  have happ : ∀ n t, t ∈ Ico (0 : ℝ) 1 → ‖stepHamiltonian H n t - H t‖ ≤ A.error n :=
    fun n t ht => A.error_bound n t ⟨ht.1, ht.2.le⟩
  have hfB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(F n).lift t‖ ≤ A.bound :=
    fun n t _ => A.forward_bound n t
  have hbB : ∀ n t, t ∈ Icc (0 : ℝ) 1 → ‖(F n).inverseLift t‖ ≤ A.bound :=
    fun n t _ => A.inverse_bound n t
  obtain ⟨U, hU0, hU, hlim, hlimadj⟩ :=
    exists_unitary_limit_of_right_approximations F A.error_limit happ hfB hbB
  have hUc : ∀ x : E, ContinuousOn (fun t => U t x) (Icc (0 : ℝ) 1) :=
    continuousOn_right_approximation_limit F A.error_limit happ hfB U hU hlim
  have hex (t : Icc (0 : ℝ) 1) : ∃ V W : D →L[ℂ] D,
      (∀ x, U t (domain.inclusion x) = domain.inclusion (V x)) ∧
      (∀ x, star (U t) (domain.inclusion x) = domain.inclusion (W x)) := by
    obtain ⟨V, hV⟩ := exists_limit_domain_lift domain (H 0) (hH 0 (by simp))
      (fun n => (F n).evolution t) (fun n => (F n).lift t)
      (fun n => (F n).preserves_domain t t.2) (fun n => hfB n t t.2)
      (U t) (hU t t.2) (hlim t t.2)
    obtain ⟨W, hW⟩ := exists_limit_domain_lift domain (H 0) (hH 0 (by simp))
      (fun n => star ((F n).evolution t)) (fun n => (F n).inverseLift t)
      (fun n => (F n).inverse_preserves_domain t t.2) (fun n => hbB n t t.2)
      (star (U t)) (Unitary.star_mem (hU t t.2)) (hlimadj t t.2)
    exact ⟨V, W, hV, hW⟩
  choose V₀ W₀ hV₀ hW₀ using hex
  let V : ℝ → D →L[ℂ] D := fun t => V₀ (projIcc 0 1 zero_le_one t)
  let W : ℝ → D →L[ℂ] D := fun t => W₀ (projIcc 0 1 zero_le_one t)
  have hV : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      U t (domain.inclusion x) = domain.inclusion (V t x) := by
    intro t ht x
    simpa only [V, projIcc_of_mem _ ht] using hV₀ ⟨t, ht⟩ x
  have hW : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      star (U t) (domain.inclusion x) = domain.inclusion (W t x) := by
    intro t ht x
    simpa only [W, projIcc_of_mem _ ht] using hW₀ ⟨t, ht⟩ x
  obtain ⟨L, hLip⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hLip' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H s - H t‖ ≤ (L : ℝ) * |s - t| := by
    intro s hs t ht
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul s hs t ht
  exact ⟨{
    evolution := U
    lift := V
    inverseLift := W
    initial := hU0
    isUnitary := hU
    preserves_domain := hV
    inverse_preserves_domain := hW
    strong_continuous := hUc
    domain_continuous := A.continuousOn_limit_lift hH U V W hU hV hW hUc hlim hlimadj
    strong_derivative := fun x t ht => by
      simpa only [ContinuousLinearMap.zero_apply, add_zero] using
        hasDerivWithinAt_right_approximation_limit F A.error_limit L.coe_nonneg hLip'
          happ hfB U V hV hlim hH hz x ht
  }⟩

end Adiabatic.Unbounded
