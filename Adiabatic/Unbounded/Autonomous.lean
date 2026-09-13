import Adiabatic.Unbounded.Domain
import Adiabatic.Unbounded.StrongCalculus
import Adiabatic.Unbounded.Resolvent
import Adiabatic.Unbounded.ResolventApproximation
import Adiabatic.Unbounded.Propagator
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Tactic

/-!
# Autonomous unitary evolution from bounded approximations

Bounded skew-adjoint operators have explicit unitary exponential groups.
For commuting generators the difference between their evolutions on a
vector is controlled by the difference of the generators on that vector,
with no operator-norm bound on either generator. This is the estimate needed
to pass from bounded resolvent approximations to unbounded autonomous
evolution. Strong limits give an actual continuous unitary group and its
domain derivative; commutation with a fixed resolvent supplies domain lifts.
The approximation hypotheses are instantiated by the self-adjoint resolvent
construction to obtain autonomous evolution from self-adjointness alone.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set NormedSpace Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : NormedAlgebra ℚ (E →L[ℂ] E) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)

/-- Exponential evolution for a bounded generator, parametrized by real time. -/
def boundedAutonomous (B : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := exp (t • B)

omit [CompleteSpace E] in
@[simp] theorem boundedAutonomous_zero (B : E →L[ℂ] E) : boundedAutonomous B 0 = 1 := by
  simp [boundedAutonomous]

/-- A single bounded generator gives an exact group on the whole real line. -/
theorem boundedAutonomous_add (B : E →L[ℂ] E) (s t : ℝ) :
    boundedAutonomous B (s + t) = boundedAutonomous B s * boundedAutonomous B t := by
  simp only [boundedAutonomous, add_smul]
  exact exp_add_of_commute (((Commute.refl B).smul_left s).smul_right t)

/-- Skew-adjoint bounded generators yield unitary exponential evolution. -/
theorem boundedAutonomous_mem_unitary {B : E →L[ℂ] E} (hB : star B = -B) (t : ℝ) :
    boundedAutonomous B t ∈ unitary (E →L[ℂ] E) := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp only [star_smul, star_trivial, hB, smul_neg]

/-- The derivative can be written with the generator on the right. -/
theorem boundedAutonomous_hasDerivAt (B : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (boundedAutonomous B) (boundedAutonomous B t * B) t :=
  hasDerivAt_exp_smul_const B t

/-- Strong differentiation of bounded autonomous evolution on a vector. -/
theorem boundedAutonomous_apply_hasDerivAt (B : E →L[ℂ] E) (x : E) (t : ℝ) :
    HasDerivAt (fun u => boundedAutonomous B u x) (boundedAutonomous B t (B x)) t := by
  exact ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t (boundedAutonomous_hasDerivAt B t)

/-- Unitary autonomous evolution moves a vector at speed at most the norm
of its image under the generator. -/
theorem norm_boundedAutonomous_apply_sub_le {B : E →L[ℂ] E} (hB : star B = -B)
    (x : E) (t : ℝ) : ‖boundedAutonomous B t x - x‖ ≤ |t| * ‖B x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := univ) (x := (0 : ℝ)) (y := t)
    (fun u _ => (boundedAutonomous_apply_hasDerivAt B x u).hasDerivWithinAt)
    (fun u _ => (ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary hB u) (B x)).le)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ 0) (mem_univ t)
  simpa [Real.norm_eq_abs, mul_comm] using h

/-- Commuting skew-adjoint generators have evolution differences controlled
on each individual vector, independently of their operator norms. -/
theorem norm_boundedAutonomous_sub_apply_le {B C : E →L[ℂ] E}
    (hB : star B = -B) (hC : star C = -C) (hBC : Commute B C) (x : E) (t : ℝ) :
    ‖boundedAutonomous B t x - boundedAutonomous C t x‖ ≤ |t| * ‖B x - C x‖ := by
  have hD : star (B - C) = -(B - C) := by rw [star_sub, hB, hC]; abel
  have hcomm : Commute C (B - C) := hBC.symm.sub_right (Commute.refl C)
  have hsplit : boundedAutonomous B t = boundedAutonomous C t * boundedAutonomous (B - C) t := by
    rw [boundedAutonomous, boundedAutonomous, boundedAutonomous, ← exp_add_of_commute
      ((hcomm.smul_left t).smul_right t), ← smul_add]
    congr 2
    abel
  calc
    ‖boundedAutonomous B t x - boundedAutonomous C t x‖ =
        ‖boundedAutonomous C t (boundedAutonomous (B - C) t x - x)‖ := by
      rw [hsplit, ContinuousLinearMap.mul_apply, map_sub]
    _ = ‖boundedAutonomous (B - C) t x - x‖ :=
      ContinuousLinearMap.norm_map_of_mem_unitary (boundedAutonomous_mem_unitary hC t) _
    _ ≤ |t| * ‖(B - C) x‖ := norm_boundedAutonomous_apply_sub_le hD x t
    _ = |t| * ‖B x - C x‖ := rfl

omit [CompleteSpace E] in
/-- Cauchy behavior on a dense set extends to every vector for a sequence
of linear isometries. -/
theorem cauchySeq_apply_of_dense_isometries {D : Type*} {j : D → E}
    (hj : DenseRange j) {U : ℕ → E →L[ℂ] E}
    (hU : ∀ n x, ‖U n x‖ = ‖x‖)
    (hc : ∀ x, CauchySeq (fun n => U n (j x))) (x : E) :
    CauchySeq (fun n => U n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := hj.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc y) (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hd (k : ℕ) : dist (U k x) (U k (j y)) = dist x (j y) := by
    simp only [dist_eq_norm, ← map_sub, hU]
  calc
    dist (U m x) (U n x) ≤ dist (U m x) (U m (j y)) + dist (U m (j y)) (U n x) :=
      dist_triangle _ _ _
    _ ≤
        dist (U m x) (U m (j y)) + dist (U m (j y)) (U n (j y)) +
          dist (U n (j y)) (U n x) :=
      by linarith [dist_triangle (U m (j y)) (U n (j y)) (U n x)]
    _ < ε := by rw [hd m, dist_comm (U n (j y)), hd n]; linarith [hN m hm n hn]

/-- Commuting skew-adjoint approximations whose generators are Cauchy on
a dense domain have strong Cauchy exponential evolutions. -/
theorem cauchySeq_boundedAutonomous_apply {D : Type*} {j : D → E}
    (hj : DenseRange j) {B : ℕ → E →L[ℂ] E}
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hc : ∀ x, CauchySeq (fun n => B n (j x))) (t : ℝ) (x : E) :
    CauchySeq (fun n => boundedAutonomous (B n) t x) := by
  apply cauchySeq_apply_of_dense_isometries hj
    (fun n y => ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary (hB n) t) y) ?_ x
  intro y
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hden : 0 < |t| + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc y) (ε / (|t| + 1)) (by positivity)
  refine ⟨N, ?_⟩
  intro m hm n hn
  calc
    dist (boundedAutonomous (B m) t (j y)) (boundedAutonomous (B n) t (j y)) ≤
        |t| * dist (B m (j y)) (B n (j y)) := by
      simpa only [dist_eq_norm] using norm_boundedAutonomous_sub_apply_le
        (hB m) (hB n) (hcomm m n) (j y) t
    _ ≤ (|t| + 1) * dist (B m (j y)) (B n (j y)) := by gcongr; linarith
    _ < ε := by
      have hh := mul_lt_mul_of_pos_left (hN m hm n hn) hden
      simpa only [mul_div_cancel₀ _ hden.ne'] using hh

/-- Bounded commuting skew-adjoint approximations produce a strong limit
on the entire Hilbert space from Cauchy behavior on a dense domain. -/
theorem exists_strong_autonomous_limit {D : Type*} {j : D → E}
    (hj : DenseRange j) {B : ℕ → E →L[ℂ] E}
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hc : ∀ x, CauchySeq (fun n => B n (j x))) :
    ∃ U : ℝ → E →L[ℂ] E, ∀ t x,
      Tendsto (fun n => boundedAutonomous (B n) t x) atTop (𝓝 (U t x)) := by
  have hex : ∀ t x, ∃ u : E,
      Tendsto (fun n => boundedAutonomous (B n) t x) atTop (𝓝 u) :=
    fun t x => cauchySeq_tendsto_of_complete
      (cauchySeq_boundedAutonomous_apply hj hB hcomm hc t x)
  choose u hu using hex
  have hbounded (t : ℝ) : Bornology.IsBounded (range (fun n => boundedAutonomous (B n) t)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary (hB n) t) x]
  exact ⟨fun t => ContinuousLinearMap.ofTendstoOfBoundedRange (u t)
    (fun n => boundedAutonomous (B n) t) (tendsto_pi_nhds.mpr (hu t)) (hbounded t), hu⟩

section StrongLimit

variable {B : ℕ → E →L[ℂ] E} {U : ℝ → E →L[ℂ] E}
  (hB : ∀ n, star (B n) = -B n)
  (hlim : ∀ t x, Tendsto (fun n => boundedAutonomous (B n) t x) atTop (𝓝 (U t x)))

include hB hlim

/-- A strong limit of the unitary approximations preserves vector norms. -/
theorem strong_autonomous_limit_norm (t : ℝ) (x : E) : ‖U t x‖ = ‖x‖ := by
  apply tendsto_nhds_unique (hlim t x).norm
  simpa only [ContinuousLinearMap.norm_map_of_mem_unitary
    (boundedAutonomous_mem_unitary (hB _) t)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))

omit hB [CompleteSpace E] in
@[simp] theorem strong_autonomous_limit_zero : U 0 = 1 := by
  ext x
  apply tendsto_nhds_unique (hlim 0 x)
  simpa only [boundedAutonomous_zero, ContinuousLinearMap.one_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

/-- The group law passes to the strong limit using the uniform bound one. -/
theorem strong_autonomous_limit_add (s t : ℝ) : U (s + t) = U s * U t := by
  ext x
  have hbound : ∀ᶠ n in atTop, ‖boundedAutonomous (B n) s‖ ≤ 1 := by
    apply Eventually.of_forall
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary (hB n) s) y]
  have hprod := tendsto_apply_of_strong hbound (hlim s (U t x)) (hlim t x)
  apply tendsto_nhds_unique (hlim (s + t) x)
  simpa only [boundedAutonomous_add, ContinuousLinearMap.mul_apply] using hprod

/-- Both inverse identities survive in the strong limit, so the limit is
unitary, rather than merely an isometry. -/
theorem strong_autonomous_limit_mem_unitary (t : ℝ) : U t ∈ unitary (E →L[ℂ] E) := by
  have hleft : star (U t) * U t = 1 :=
    (U t).norm_map_iff_adjoint_comp_self.mp (strong_autonomous_limit_norm hB hlim t)
  have hright : U t * U (-t) = 1 := by
    rw [← strong_autonomous_limit_add hB hlim, add_neg_cancel, strong_autonomous_limit_zero hlim]
  apply Unitary.mem_iff.mpr ⟨hleft, ?_⟩
  calc
    U t * star (U t) = (U t * star (U t)) * (U t * U (-t)) := by rw [hright, mul_one]
    _ = U t * (star (U t) * U t) * U (-t) := by noncomm_ring
    _ = 1 := by rw [hleft, mul_one, hright]

/-- A bound on the approximating generators at one vector gives a Lipschitz
bound on the limiting orbit of that vector. -/
theorem strong_autonomous_limit_dist_le (x : E) {M : ℝ}
    (hM : ∀ n, ‖B n x‖ ≤ M) (s t : ℝ) :
    dist (U s x) (U t x) ≤ M * dist s t := by
  apply le_of_tendsto ((hlim s x).dist (hlim t x))
  apply Eventually.of_forall
  intro n
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := univ) (x := t) (y := s)
    (fun u _ => (boundedAutonomous_apply_hasDerivAt (B n) x u).hasDerivWithinAt)
    (fun u _ => (ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary (hB n) u) (B n x)).le.trans (hM n))
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ t) (mem_univ s)
  simpa only [dist_eq_norm] using h

/-- The limiting group is strongly continuous: bounded generator orbits
on a dense set suffice, with no uniform bound on the generator norms. -/
theorem strong_autonomous_limit_continuous {D : Type*} {j : D → E}
    (hj : DenseRange j) (hc : ∀ y, CauchySeq (fun n => B n (j y))) (x : E) :
    Continuous (fun t => U t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := hj.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (hc y).isBounded_range
  have hM' : ∀ n, ‖B n (j y)‖ ≤ M := fun n => hM _ (mem_range_self n)
  have hMnonneg : 0 ≤ M := (norm_nonneg (B 0 (j y))).trans (hM' 0)
  have hMpos : 0 < 3 * (M + 1) := by positivity
  refine ⟨ε / (3 * (M + 1)), by positivity, ?_⟩
  intro s hs
  have hd (r : ℝ) : dist (U r x) (U r (j y)) = dist x (j y) := by
    simp only [dist_eq_norm, ← map_sub, strong_autonomous_limit_norm hB hlim]
  have hsmall : M * dist s t < ε / 3 := by
    have h := (lt_div_iff₀ hMpos).mp hs
    nlinarith [dist_nonneg (x := s) (y := t)]
  have hdomain := strong_autonomous_limit_dist_le hB hlim (j y) hM' s t
  calc
    dist (U s x) (U t x) ≤ dist (U s x) (U s (j y)) + dist (U s (j y)) (U t x) :=
      dist_triangle _ _ _
    _ ≤ dist (U s x) (U s (j y)) + dist (U s (j y)) (U t (j y)) +
        dist (U t (j y)) (U t x) := by
      linarith [dist_triangle (U s (j y)) (U t (j y)) (U t x)]
    _ < ε := by rw [hd s, dist_comm (U t (j y)), hd t]; linarith

/-- The vector comparison bound persists when one approximating generator
is replaced by its strong limit on a fixed vector. -/
theorem strong_autonomous_limit_approximation_bound
    (hcomm : ∀ m n, Commute (B m) (B n)) {x g : E}
    (hg : Tendsto (fun n => B n x) atTop (𝓝 g)) (n : ℕ) (t : ℝ) :
    dist (boundedAutonomous (B n) t x) (U t x) ≤ |t| * dist (B n x) g := by
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.dist (hlim t x))
    ((tendsto_const_nhds.dist hg).const_mul |t|)
  apply Eventually.of_forall
  intro m
  simpa only [dist_eq_norm] using
    norm_boundedAutonomous_sub_apply_le (hB n) (hB m) (hcomm n m) x t

/-- Strong convergence of these exponential approximations is uniform on
every bounded time set, including for vectors outside the generator domain. -/
theorem strong_autonomous_limit_uniformOn {D : Type*} {j : D → E}
    (hj : DenseRange j) (hcomm : ∀ m n, Commute (B m) (B n))
    (hc : ∀ y, CauchySeq (fun n => B n (j y))) (x : E)
    {s : Set ℝ} {R : ℝ} (hR : 0 ≤ R) (hs : ∀ t ∈ s, |t| ≤ R) :
    TendstoUniformlyOn (fun n t => boundedAutonomous (B n) t x) (fun t => U t x) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := hj.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (hc y)
  have hsmall : ∀ᶠ n in atTop, dist (B n (j y)) g < ε / (3 * (R + 1)) :=
    Metric.tendsto_nhds.mp hg _ (by positivity)
  filter_upwards [hsmall] with n hn t ht
  have hbound := strong_autonomous_limit_approximation_bound hB hlim hcomm hg n t
  have hmid : dist (boundedAutonomous (B n) t (j y)) (U t (j y)) < ε / 3 := by
    have hden : 0 < 3 * (R + 1) := by positivity
    have hh := (lt_div_iff₀ hden).mp hn
    have hb : |t| * dist (B n (j y)) g ≤ R * dist (B n (j y)) g := by gcongr; exact hs t ht
    nlinarith [dist_nonneg (x := B n (j y)) (y := g)]
  have hd₁ : dist (boundedAutonomous (B n) t x) (boundedAutonomous (B n) t (j y)) =
      dist x (j y) := by
    simp only [dist_eq_norm, ← map_sub, ContinuousLinearMap.norm_map_of_mem_unitary
      (boundedAutonomous_mem_unitary (hB n) t)]
  have hd₂ : dist (U t (j y)) (U t x) = dist x (j y) := by
    rw [dist_comm]
    simp only [dist_eq_norm, ← map_sub, strong_autonomous_limit_norm hB hlim]
  have htri := dist_triangle (boundedAutonomous (B n) t x)
    (boundedAutonomous (B n) t (j y)) (U t x)
  have htri₂ := dist_triangle (boundedAutonomous (B n) t (j y)) (U t (j y)) (U t x)
  rw [hd₁] at htri
  rw [hd₂] at htri₂
  rw [dist_comm]
  linarith

/-- Convergence of generators on a vector passes the strong derivative to
the limiting unitary group. -/
theorem strong_autonomous_limit_hasDerivAt {D : Type*} {j : D → E}
    (hj : DenseRange j) (hcomm : ∀ m n, Commute (B m) (B n))
    (hc : ∀ y, CauchySeq (fun n => B n (j y))) {x g : E}
    (hg : Tendsto (fun n => B n x) atTop (𝓝 g)) (t : ℝ) :
    HasDerivAt (fun u => U u x) (U t g) t := by
  let R : ℝ := |t| + 1
  let s : Set ℝ := Ioo (-R) R
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : ∀ u ∈ s, |u| ≤ R := fun u hu => abs_le.mpr ⟨hu.1.le, hu.2.le⟩
  have hunif := strong_autonomous_limit_uniformOn hB hlim hj hcomm hc g hR hs
  have hderiv : TendstoUniformlyOn
      (fun n u => boundedAutonomous (B n) u (B n x)) (fun u => U u g) atTop s := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    intro ε hε
    have hgsmall : ∀ᶠ n in atTop, dist (B n x) g < ε / 2 :=
      Metric.tendsto_nhds.mp hg (ε / 2) (by positivity)
    filter_upwards [hgsmall, hunif (ε / 2) (by positivity)] with n hn hnu u hu
    have hfirst : dist (boundedAutonomous (B n) u (B n x)) (boundedAutonomous (B n) u g) =
        dist (B n x) g := by
      simp only [dist_eq_norm, ← map_sub, ContinuousLinearMap.norm_map_of_mem_unitary
        (boundedAutonomous_mem_unitary (hB n) u)]
    have hh := dist_triangle (boundedAutonomous (B n) u (B n x))
      (boundedAutonomous (B n) u g) (U u g)
    rw [hfirst] at hh
    have hun := hnu u hu
    rw [dist_comm] at hun ⊢
    linarith
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hderiv
    (Eventually.of_forall (fun n u _ => boundedAutonomous_apply_hasDerivAt (B n) x u))
    (fun u _ => hlim u x)
  change -(|t| + 1) < t ∧ t < |t| + 1
  constructor <;> linarith [le_abs_self t, neg_abs_le t]

omit hB [CompleteSpace E] in
/-- Commutation with a fixed bounded operator survives a strong limit. -/
theorem strong_autonomous_limit_commute (R : E →L[ℂ] E)
    (hBR : ∀ n, Commute (B n) R) (t : ℝ) : Commute (U t) R := by
  change U t * R = R * U t
  ext x
  apply tendsto_nhds_unique (hlim t (R x))
  have h := R.continuous.tendsto (U t x) |>.comp (hlim t x)
  apply h.congr'
  apply Eventually.of_forall
  intro n
  exact (congrArg (fun A : E →L[ℂ] E => A x) (((hBR n).smul_left t).exp_left.eq)).symm

/-- The inverse of the limiting group is its adjoint. -/
theorem strong_autonomous_limit_star (t : ℝ) : star (U t) = U (-t) := by
  have hleft := Unitary.star_mul_self_of_mem (strong_autonomous_limit_mem_unitary hB hlim t)
  have hright : U t * U (-t) = 1 := by
    rw [← strong_autonomous_limit_add hB hlim, add_neg_cancel, strong_autonomous_limit_zero hlim]
  calc
    star (U t) = star (U t) * (U t * U (-t)) := by rw [hright, mul_one]
    _ = U (-t) := by rw [← mul_assoc, hleft, one_mul]

end StrongLimit

/-- A family of mutually commuting skew-adjoint bounded approximations,
Cauchy on a dense domain, constructs a unitary group by strong limits. -/
theorem exists_unitary_autonomous_limit {D : Type*} {j : D → E}
    (hj : DenseRange j) {B : ℕ → E →L[ℂ] E}
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hc : ∀ x, CauchySeq (fun n => B n (j x))) :
    ∃ U : ℝ → E →L[ℂ] E,
      (∀ t x, Tendsto (fun n => boundedAutonomous (B n) t x) atTop (𝓝 (U t x))) ∧
      U 0 = 1 ∧ (∀ s t, U (s + t) = U s * U t) ∧
      (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ ∀ x, Continuous (fun t => U t x) := by
  obtain ⟨U, hlim⟩ := exists_strong_autonomous_limit hj hB hcomm hc
  exact ⟨U, hlim, strong_autonomous_limit_zero hlim,
    strong_autonomous_limit_add hB hlim, strong_autonomous_limit_mem_unitary hB hlim,
    strong_autonomous_limit_continuous hB hlim hj hc⟩

namespace CommonDomain

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  (domain : CommonDomain D E) (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)

/-- Lift a physical operator to the common domain using a nonreal resolvent.
Commutation with that resolvent will imply domain preservation. -/
def autonomousLift (w : ℂ) (hw : w.im ≠ 0) (U : E →L[ℂ] E) : D →L[ℂ] D :=
  (domain.resolvent H hH w hw).comp (U.comp (domain.shift H w))

/-- Commutation with a nonreal resolvent implies preservation of the full
unbounded operator domain. -/
theorem autonomousLift_preserves (w : ℂ) (hw : w.im ≠ 0) (U : E →L[ℂ] E)
    (hcomm : Commute U (domain.physicalResolvent H hH w hw)) (x : D) :
    U (domain.inclusion x) = domain.inclusion (domain.autonomousLift H hH w hw U x) := by
  change U (domain.inclusion x) = domain.physicalResolvent H hH w hw (U (domain.shift H w x))
  rw [← ContinuousLinearMap.mul_apply, ← hcomm.eq, ContinuousLinearMap.mul_apply]
  simp only [physicalResolvent_apply, resolvent_shift]

/-- The domain lift of a resolvent-commuting operator also commutes with
the unbounded Hamiltonian on its domain. -/
theorem autonomousLift_map (w : ℂ) (hw : w.im ≠ 0) (U : E →L[ℂ] E)
    (hcomm : Commute U (domain.physicalResolvent H hH w hw)) (x : D) :
    H (domain.autonomousLift H hH w hw U x) = U (H x) := by
  have hshift : domain.shift H w (domain.autonomousLift H hH w hw U x) =
      U (domain.shift H w x) := domain.shift_resolvent H hH w hw _
  rw [shift_apply, shift_apply, map_sub, map_smul,
    domain.autonomousLift_preserves H hH w hw U hcomm x] at hshift
  exact sub_left_inj.mp hshift

/-- Autonomous evolution on the whole real line, including domain
continuity and the strong derivative for both positive and negative time. -/
structure AutonomousGroup (z : ℂ) where
  evolution : ℝ → E →L[ℂ] E
  lift : ℝ → D →L[ℂ] D
  initial : evolution 0 = 1
  isUnitary : ∀ t, evolution t ∈ unitary (E →L[ℂ] E)
  group_law : ∀ s t, evolution (s + t) = evolution s * evolution t
  preserves_domain : ∀ t x, evolution t (domain.inclusion x) = domain.inclusion (lift t x)
  commutes : ∀ t x, H (lift t x) = evolution t (H x)
  strong_continuous : ∀ x, Continuous (fun t => evolution t x)
  domain_continuous : ∀ x, Continuous (fun t => lift t x)
  strong_derivative : ∀ x t, HasDerivAt (fun a => evolution a (domain.inclusion x))
    (z • H (lift t x)) t

variable {domain H}

omit [CompleteSpace D] in
/-- The inverse of an autonomous unitary group is its negative-time value. -/
theorem AutonomousGroup.star_eq_neg {z : ℂ} (U : domain.AutonomousGroup H z) (t : ℝ) :
    star (U.evolution t) = U.evolution (-t) := by
  have hleft := Unitary.star_mul_self_of_mem (U.isUnitary t)
  have hright : U.evolution t * U.evolution (-t) = 1 := by
    rw [← U.group_law, add_neg_cancel, U.initial]
  calc
    star (U.evolution t) = star (U.evolution t) * (U.evolution t * U.evolution (-t)) := by
      rw [hright, mul_one]
    _ = U.evolution (-t) := by rw [← mul_assoc, hleft, one_mul]

omit [CompleteSpace D] in
/-- Global autonomous evolutions have physical operator norm at most one. -/
theorem AutonomousGroup.norm_le_one {z : ℂ} (U : domain.AutonomousGroup H z) (t : ℝ) :
    ‖U.evolution t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ContinuousLinearMap.norm_map_of_mem_unitary (U.isUnitary t)]

omit [CompleteSpace D] in
/-- Negative-time autonomous evolution has the inverse strong derivative
on every domain vector. -/
theorem AutonomousGroup.inverse_derivative {z : ℂ} (U : domain.AutonomousGroup H z)
    (x : D) (t : ℝ) :
    HasDerivAt (fun u => U.evolution (-u) (domain.inclusion x))
      (-(z • U.evolution (-t) (H x))) t := by
  simpa only [Function.comp_def, neg_one_smul, U.commutes] using
    (U.strong_derivative x (-t)).scomp t (hasDerivAt_neg t)

/-- Restrict a global autonomous group to the unit-interval propagator API. -/
def AutonomousGroup.toStrongPropagator {z : ℂ} (U : domain.AutonomousGroup H z) :
    StrongPropagator domain (fun _ => H) (fun _ => 0) z where
  evolution := U.evolution
  lift := U.lift
  inverseLift := fun t => U.lift (-t)
  initial := U.initial
  isUnitary := fun t _ => U.isUnitary t
  preserves_domain := fun t _ => U.preserves_domain t
  inverse_preserves_domain := fun t _ x => by rw [U.star_eq_neg]; exact U.preserves_domain (-t) x
  strong_continuous := fun x => (U.strong_continuous x).continuousOn
  domain_continuous := fun x => (U.domain_continuous x).continuousOn
  strong_derivative := fun x t _ => by
    simpa only [ContinuousLinearMap.zero_apply, add_zero] using (U.strong_derivative x t).hasDerivWithinAt

variable (domain H)

/-- Construct a global autonomous group from actual commuting bounded
approximations and their domain-generator limit. -/
theorem exists_autonomousGroup_of_approximations
    (z : ℂ) (B : ℕ → E →L[ℂ] E)
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hgen : ∀ x, Tendsto (fun n => B n (domain.inclusion x)) atTop (𝓝 (z • H x)))
    (hres : ∀ n, Commute (B n) (domain.physicalResolvent H hH Complex.I (by simp))) :
    Nonempty (domain.AutonomousGroup H z) := by
  have hc := fun x => (hgen x).cauchySeq
  obtain ⟨U, hlim, hU0, hUadd, hUunitary, hUcont⟩ :=
    exists_unitary_autonomous_limit domain.dense hB hcomm hc
  have hUres (t : ℝ) := strong_autonomous_limit_commute hlim
    (domain.physicalResolvent H hH Complex.I (by simp)) hres t
  let V : ℝ → D →L[ℂ] D := fun t => domain.autonomousLift H hH Complex.I (by simp) (U t)
  refine ⟨{
    evolution := U
    lift := V
    initial := hU0
    isUnitary := hUunitary
    group_law := hUadd
    preserves_domain := fun t x => domain.autonomousLift_preserves H hH _ _ _ (hUres t) x
    commutes := fun t x => domain.autonomousLift_map H hH _ _ _ (hUres t) x
    strong_continuous := hUcont
    domain_continuous := fun x =>
      (domain.resolvent H hH Complex.I (by simp)).continuous.comp
        (hUcont (domain.shift H Complex.I x))
    strong_derivative := ?_
  }⟩
  intro x t
  have hd := strong_autonomous_limit_hasDerivAt hB hlim domain.dense hcomm hc (hgen x) t
  have hmap := domain.autonomousLift_map H hH Complex.I (by simp) (U t) (hUres t) x
  simpa only [map_smul, ← hmap] using hd

include hH in
/-- Every self-adjoint common-domain Hamiltonian generates a unitary group
for every purely imaginary scaling, with a global strong domain derivative. -/
theorem exists_autonomousGroup (z : ℂ) (hz : star z = -z) :
    Nonempty (domain.AutonomousGroup H z) := by
  apply domain.exists_autonomousGroup_of_approximations H hH z
    (fun n => z • domain.regularizedHamiltonian H hH n)
  · intro n
    rw [star_smul, hz, domain.regularizedHamiltonian_selfAdjoint H hH n, neg_smul]
  · intro m n
    exact ((domain.regularizedHamiltonian_commute H hH m n).smul_left z).smul_right z
  · intro x
    exact (domain.tendsto_regularizedHamiltonian H hH x).const_smul z
  · intro n
    exact (domain.regularizedHamiltonian_commute_physicalResolvent H hH n Complex.I
      (by simp)).smul_left z

/-- Commuting bounded approximations construct an actual strong propagator
for an unbounded autonomous Hamiltonian. The approximations, their generator
limit and their resolvent commutation remain explicit in this intermediate theorem. -/
theorem exists_autonomous_evolution_of_approximations
    (z : ℂ) (B : ℕ → E →L[ℂ] E)
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hgen : ∀ x, Tendsto (fun n => B n (domain.inclusion x)) atTop (𝓝 (z • H x)))
    (hres : ∀ n, Commute (B n) (domain.physicalResolvent H hH Complex.I (by simp))) :
    ∃ V : StrongPropagator domain (fun _ => H) (fun _ => 0) z,
      (∀ s t, V.evolution (s + t) = V.evolution s * V.evolution t) ∧
      ∀ t x, H (V.lift t x) = V.evolution t (H x) := by
  obtain ⟨G⟩ := domain.exists_autonomousGroup_of_approximations H hH z B hB hcomm hgen hres
  exact ⟨G.toStrongPropagator, G.group_law, G.commutes⟩

/-- The approximation construction supplies a strong propagator. -/
theorem exists_autonomous_strongPropagator_of_approximations
    (z : ℂ) (B : ℕ → E →L[ℂ] E)
    (hB : ∀ n, star (B n) = -B n)
    (hcomm : ∀ m n, Commute (B m) (B n))
    (hgen : ∀ x, Tendsto (fun n => B n (domain.inclusion x)) atTop (𝓝 (z • H x)))
    (hres : ∀ n, Commute (B n) (domain.physicalResolvent H hH Complex.I (by simp))) :
    Nonempty (StrongPropagator domain (fun _ => H) (fun _ => 0) z) := by
  obtain ⟨V, _, _⟩ := domain.exists_autonomous_evolution_of_approximations H hH z B hB hcomm hgen hres
  exact ⟨V⟩

include hH in
/-- Self-adjointness produces a strong unitary evolution with its exact
group law and commutation with the unbounded Hamiltonian on the domain. -/
theorem exists_autonomous_evolution (z : ℂ) (hz : star z = -z) :
    ∃ V : StrongPropagator domain (fun _ => H) (fun _ => 0) z,
      (∀ s t, V.evolution (s + t) = V.evolution s * V.evolution t) ∧
      ∀ t x, H (V.lift t x) = V.evolution t (H x) := by
  apply domain.exists_autonomous_evolution_of_approximations H hH z
    (fun n => z • domain.regularizedHamiltonian H hH n)
  · intro n
    rw [star_smul, hz, domain.regularizedHamiltonian_selfAdjoint H hH n, neg_smul]
  · intro m n
    exact ((domain.regularizedHamiltonian_commute H hH m n).smul_left z).smul_right z
  · intro x
    exact (domain.tendsto_regularizedHamiltonian H hH x).const_smul z
  · intro n
    exact (domain.regularizedHamiltonian_commute_physicalResolvent H hH n Complex.I
      (by simp)).smul_left z

include hH in
/-- Every self-adjoint common-domain Hamiltonian generates an actual
domain-preserving unitary strong evolution. In particular `z = -i T` gives
Schrödinger evolution for every real runtime. No propagator, spectral
decomposition or evolution estimate is assumed. -/
theorem exists_autonomous_strongPropagator (z : ℂ) (hz : star z = -z) :
    Nonempty (StrongPropagator domain (fun _ => H) (fun _ => 0) z) := by
  obtain ⟨V, _, _⟩ := domain.exists_autonomous_evolution H hH z hz
  exact ⟨V⟩

end CommonDomain

end Adiabatic.Unbounded
