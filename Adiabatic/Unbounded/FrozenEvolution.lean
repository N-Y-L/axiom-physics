import Adiabatic.Unbounded.RightPropagator
import Adiabatic.Unbounded.Autonomous
import Adiabatic.Unbounded.TimeSlicing
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Frozen Hamiltonian evolutions on a uniform time grid

Each factor runs for a clipped elapsed time. Consequently the product is
continuous at grid points, while its right derivative uses the frozen
Hamiltonian for the following cell.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Filter
open scoped Topology

/-- The mesh is positive for every natural index. -/
def gridMesh (n : ℕ) : ℝ := 1 / (n + 1 : ℕ)

theorem gridMesh_pos (n : ℕ) : 0 < gridMesh n := by
  unfold gridMesh
  positivity

theorem gridMesh_le_one (n : ℕ) : gridMesh n ≤ 1 := by
  unfold gridMesh
  apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- A sample time, clipped at the endpoint so every frozen Hamiltonian is
selected within the interval where self-adjointness is known. -/
def gridSample (n k : ℕ) : ℝ := min (k * gridMesh n) 1

theorem gridSample_mem (n k : ℕ) : gridSample n k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (mul_nonneg (Nat.cast_nonneg k) (gridMesh_pos n).le) zero_le_one
  · exact min_le_right _ _

/-- Time spent in one cell up to physical time `t`. -/
def gridDuration (n k : ℕ) (t : ℝ) : ℝ :=
  min (max (t - k * gridMesh n) 0) (gridMesh n)

theorem gridDuration_mem (n k : ℕ) (t : ℝ) : gridDuration n k t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (le_max_right _ _) (gridMesh_pos n).le
  · exact (min_le_right _ _).trans (gridMesh_le_one n)

theorem gridDuration_continuous (n k : ℕ) : Continuous (gridDuration n k) := by
  exact ((continuous_id.sub continuous_const).max continuous_const).min continuous_const

@[simp] theorem gridDuration_zero (n k : ℕ) : gridDuration n k 0 = 0 := by
  have hk : 0 ≤ (k : ℝ) * gridMesh n := mul_nonneg (Nat.cast_nonneg k) (gridMesh_pos n).le
  simp only [gridDuration, zero_sub, max_eq_right (neg_nonpos.mpr hk),
    min_eq_left (gridMesh_pos n).le]

theorem gridDuration_full {n j k : ℕ} {t : ℝ}
    (hk : k < j) (ht : j * gridMesh n ≤ t) : gridDuration n k t = gridMesh n := by
  have hcast : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
  have hm := gridMesh_pos n
  have hstep : gridMesh n ≤ t - k * gridMesh n := by nlinarith
  exact min_eq_right (hstep.trans (le_max_left _ _))

theorem gridDuration_active {n j : ℕ} {t : ℝ}
    (ht : j * gridMesh n ≤ t) (ht' : t ≤ (j + 1 : ℕ) * gridMesh n) :
    gridDuration n j t = t - j * gridMesh n := by
  have hl : 0 ≤ t - j * gridMesh n := sub_nonneg.mpr ht
  have hr : t - j * gridMesh n ≤ gridMesh n := by
    push_cast at ht'
    linarith
  simp only [gridDuration, max_eq_left hl, min_eq_left hr]

theorem gridDuration_future {n j k : ℕ} {t : ℝ}
    (hk : j < k) (ht : t ≤ (j + 1 : ℕ) * gridMesh n) : gridDuration n k t = 0 := by
  have hcast : (j : ℝ) + 1 ≤ k := by exact_mod_cast hk
  have hm := gridMesh_pos n
  have hstep : t - k * gridMesh n ≤ 0 := by
    push_cast at ht
    nlinarith
  simp only [gridDuration, max_eq_right hstep, min_eq_left hm.le]

/-- The active cell index; it is used only to identify the right derivative. -/
def gridIndex (n : ℕ) (t : ℝ) : ℕ := ⌊(n + 1 : ℕ) * t⌋₊

theorem gridIndex_lt {n : ℕ} {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    gridIndex n t < n + 1 := by
  unfold gridIndex
  apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg (n + 1)) ht.1)).mpr
  exact mul_lt_of_lt_one_right (by positivity) ht.2

theorem gridIndex_bounds {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    gridIndex n t * gridMesh n ≤ t ∧ t < (gridIndex n t + 1 : ℕ) * gridMesh n := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlo := Nat.floor_le (mul_nonneg hn.le ht)
  have hhi := Nat.lt_floor_add_one ((n + 1 : ℕ) * t : ℝ)
  simp only [gridIndex, gridMesh, mul_one_div]
  constructor
  · exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hlo)
  · exact (lt_div_iff₀ hn).mpr (by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hhi)

/-- The chosen frozen time is within one mesh of the physical time. -/
theorem gridSample_index_bounds {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    gridSample n (gridIndex n t) ≤ t ∧
      |gridSample n (gridIndex n t) - t| ≤ gridMesh n := by
  obtain ⟨hlo, hhi⟩ := gridIndex_bounds ht.1
  have he : gridSample n (gridIndex n t) = gridIndex n t * gridMesh n :=
    min_eq_left (hlo.trans ht.2)
  rw [he]
  refine ⟨hlo, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  push_cast at hhi
  linarith

/-- The piecewise frozen Hamiltonian. -/
def stepHamiltonian {A : Type*} (H : ℝ → A) (n : ℕ) (t : ℝ) : A :=
  H (gridSample n (gridIndex n t))

/-- A Lipschitz Hamiltonian has a uniform one-mesh freezing error. -/
theorem norm_stepHamiltonian_sub_le {A : Type*} [NormedAddCommGroup A]
    (H : ℝ → A) {L : NNReal} (hH : LipschitzOnWith L H (Icc (0 : ℝ) 1))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖stepHamiltonian H n t - H t‖ ≤ L * gridMesh n := by
  calc
    ‖stepHamiltonian H n t - H t‖ ≤ L * |gridSample n (gridIndex n t) - t| := by
      simpa only [stepHamiltonian, dist_eq_norm, Real.norm_eq_abs] using
        hH.dist_le_mul _ (gridSample_mem n _) t ht
    _ ≤ L * gridMesh n := mul_le_mul_of_nonneg_left (gridSample_index_bounds ht).2 L.coe_nonneg

/-- Products agree when their factors agree before the final index. -/
theorem timeOrderedProduct_congr {A : Type*} [Monoid A] {a b : ℕ → A} (n : ℕ)
    (hab : ∀ k < n, a k = b k) : timeOrderedProduct a n = timeOrderedProduct b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [timeOrderedProduct_succ, timeOrderedProduct_succ, hab n (Nat.lt_succ_self n),
      ih (fun k hk => hab k (Nat.lt_succ_of_lt hk))]

/-- Identity factors after an index do not change a chronological product. -/
theorem timeOrderedProduct_one_tail {A : Type*} [Monoid A] (a : ℕ → A)
    {j n : ℕ} (hjn : j ≤ n) (ha : ∀ k, j ≤ k → a k = 1) :
    timeOrderedProduct a n = timeOrderedProduct a j := by
  induction n, hjn using Nat.le_induction with
  | base => rfl
  | succ n hjn ih => rw [timeOrderedProduct_succ, ha n hjn, one_mul, ih]

/-- Inside a cell the chronological product has one active factor. -/
theorem timeOrderedProduct_grid_eq {A : Type*} [Monoid A] (F : ℕ → ℝ → A)
    (hF : ∀ k, F k 0 = 1) {n j : ℕ} (hj : j < n + 1) {t : ℝ}
    (ht : j * gridMesh n ≤ t) (ht' : t ≤ (j + 1 : ℕ) * gridMesh n) :
    timeOrderedProduct (fun k => F k (gridDuration n k t)) (n + 1) =
      F j (t - j * gridMesh n) * timeOrderedProduct (fun k => F k (gridMesh n)) j := by
  rw [timeOrderedProduct_one_tail (fun k => F k (gridDuration n k t))
    (Nat.succ_le_of_lt hj) (fun k hk => by
      dsimp only
      rw [gridDuration_future (Nat.lt_of_succ_le hk) ht', hF])]
  rw [timeOrderedProduct_succ, gridDuration_active ht ht']
  congr 1
  exact timeOrderedProduct_congr j (fun k hk => by rw [gridDuration_full hk ht])

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite products of uniformly bounded strongly continuous families are
strongly continuous. -/
theorem continuousOn_timeOrderedProduct_apply (F : ℕ → ℝ → E →L[ℂ] E)
    (hF : ∀ k x, ContinuousOn (fun t => F k t x) (Icc (0 : ℝ) 1))
    (M : ℕ → ℝ) (hM : ∀ k t, t ∈ Icc (0 : ℝ) 1 → ‖F k t‖ ≤ M k)
    (n : ℕ) (x : E) :
    ContinuousOn (fun t => timeOrderedProduct (fun k => F k t) n x) (Icc (0 : ℝ) 1) := by
  induction n with
  | zero => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => x) (Icc (0 : ℝ) 1))
  | succ n ih =>
    intro t ht
    apply tendsto_apply_of_strong (A := F n)
      (v := fun a => timeOrderedProduct (fun k => F k a) n x)
      (M := M n)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact hM n a ha
    · exact hF n _ t ht
    · exact ih t ht

end Normed

section Hilbert

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The autonomous evolutions selected at each frozen sample. -/
structure FrozenFamily (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)
    (z : ℂ) (n : ℕ) where
  propagator : ∀ k, domain.AutonomousGroup (H (gridSample n k)) z

/-- Genuine self-adjointness supplies all frozen autonomous factors. -/
theorem exists_frozenFamily (domain : CommonDomain D E) (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (z : ℂ) (hz : star z = -z) (n : ℕ) : Nonempty (FrozenFamily domain H z n) := by
  exact ⟨⟨fun k => Classical.choice (domain.exists_autonomousGroup (H (gridSample n k))
    (hH _ (gridSample_mem n k)) z hz)⟩⟩

namespace FrozenFamily

variable {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {z : ℂ} {n : ℕ}
  (V : FrozenFamily domain H z n)

/-- Physical evolution as a finite product of clipped autonomous factors. -/
def evolution (t : ℝ) : E →L[ℂ] E :=
  timeOrderedProduct (fun k => (V.propagator k).evolution (gridDuration n k t)) (n + 1)

/-- Its common-domain lift uses the same chronological factors. -/
def lift (t : ℝ) : D →L[ℂ] D :=
  timeOrderedProduct (fun k => (V.propagator k).lift (gridDuration n k t)) (n + 1)

omit [CompleteSpace D] in
theorem preserves_domain (t : ℝ) (x : D) :
    V.evolution t (domain.inclusion x) = domain.inclusion (V.lift t x) := by
  apply timeOrderedProduct_preserves_domain
  intro k y
  exact (V.propagator k).preserves_domain _ y

omit [CompleteSpace D] in
theorem isUnitary (t : ℝ) : V.evolution t ∈ unitary (E →L[ℂ] E) := by
  apply timeOrderedProduct_mem_unitary
  intro k
  exact (V.propagator k).isUnitary _

omit [CompleteSpace D] in
@[simp] theorem initial : V.evolution 0 = 1 := by
  unfold evolution
  have he : (fun k => (V.propagator k).evolution (gridDuration n k 0)) = fun _ => 1 := by
    funext k
    rw [gridDuration_zero, (V.propagator k).initial]
  rw [he]
  induction n + 1 with
  | zero => rfl
  | succ m ih => rw [timeOrderedProduct_succ, one_mul, ih]

omit [CompleteSpace D] in
theorem strong_continuous (x : E) :
    ContinuousOn (fun t => V.evolution t x) (Icc (0 : ℝ) 1) := by
  refine continuousOn_timeOrderedProduct_apply
    (fun k t => (V.propagator k).evolution (gridDuration n k t)) ?_ (fun _ => 1) ?_ (n + 1) x
  · intro k y
    exact (((V.propagator k).strong_continuous y).comp
      (gridDuration_continuous n k)).continuousOn
  · intro k t _
    exact (V.propagator k).toStrongPropagator.norm_le_one (gridDuration_mem n k t)

omit [CompleteSpace D] in
/-- A frozen factor preserves its own shifted graph norm. -/
theorem shift_lift (k : ℕ) (t : ℝ) (x : D) :
    domain.shift (H (gridSample n k)) Complex.I ((V.propagator k).lift t x) =
      (V.propagator k).evolution t (domain.shift (H (gridSample n k)) Complex.I x) := by
  simp only [CommonDomain.shift_apply, (V.propagator k).commutes, map_sub, map_smul,
    (V.propagator k).preserves_domain t]

/-- A uniform bound in the domain norm for one frozen factor. -/
theorem norm_factor_lift_le
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t))
    (k : ℕ) (t : ℝ) :
    ‖(V.propagator k).lift t‖ ≤
      ‖domain.inverseShift (H (gridSample n k)) Complex.I‖ *
        ‖domain.shift (H (gridSample n k)) Complex.I‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hp := domain.mem_resolventSet_of_im_ne_zero (H (gridSample n k))
    (hH _ (gridSample_mem n k)) Complex.I (by simp)
  calc
    ‖(V.propagator k).lift t x‖ =
        ‖domain.inverseShift (H (gridSample n k)) Complex.I
          (domain.shift (H (gridSample n k)) Complex.I ((V.propagator k).lift t x))‖ := by
      rw [domain.inverseShift_shift _ _ hp]
    _ ≤ ‖domain.inverseShift (H (gridSample n k)) Complex.I‖ *
        ‖domain.shift (H (gridSample n k)) Complex.I ((V.propagator k).lift t x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖domain.inverseShift (H (gridSample n k)) Complex.I‖ *
        ‖domain.shift (H (gridSample n k)) Complex.I x‖ := by
      rw [V.shift_lift k t, ContinuousLinearMap.norm_map_of_mem_unitary
        ((V.propagator k).isUnitary t)]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)

theorem domain_continuous
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) (x : D) :
    ContinuousOn (fun t => V.lift t x) (Icc (0 : ℝ) 1) := by
  refine continuousOn_timeOrderedProduct_apply
    (fun k t => (V.propagator k).lift (gridDuration n k t)) ?_
    (fun k => ‖domain.inverseShift (H (gridSample n k)) Complex.I‖ *
      ‖domain.shift (H (gridSample n k)) Complex.I‖) ?_ (n + 1) x
  · intro k y
    exact (((V.propagator k).domain_continuous y).comp
      (gridDuration_continuous n k)).continuousOn
  · intro k t _
    exact V.norm_factor_lift_le hH k (gridDuration n k t)

omit [CompleteSpace D] in
@[simp] theorem factor_lift_zero (k : ℕ) : (V.propagator k).lift 0 = 1 := by
  ext x
  apply domain.injective
  rw [← (V.propagator k).preserves_domain, (V.propagator k).initial]
  rfl

omit [CompleteSpace D] in
/-- On one grid cell all completed factors are fixed. -/
theorem evolution_eq_cell {j : ℕ} (hj : j < n + 1) {t : ℝ}
    (ht : j * gridMesh n ≤ t) (ht' : t ≤ (j + 1 : ℕ) * gridMesh n) :
    V.evolution t = (V.propagator j).evolution (t - j * gridMesh n) *
      timeOrderedProduct (fun k => (V.propagator k).evolution (gridMesh n)) j :=
  timeOrderedProduct_grid_eq _ (fun k => (V.propagator k).initial) hj ht ht'

omit [CompleteSpace D] in
/-- The domain lift has the same cell decomposition. -/
theorem lift_eq_cell {j : ℕ} (hj : j < n + 1) {t : ℝ}
    (ht : j * gridMesh n ≤ t) (ht' : t ≤ (j + 1 : ℕ) * gridMesh n) :
    V.lift t = (V.propagator j).lift (t - j * gridMesh n) *
      timeOrderedProduct (fun k => (V.propagator k).lift (gridMesh n)) j :=
  timeOrderedProduct_grid_eq _ V.factor_lift_zero hj ht ht'

omit [CompleteSpace D] in
/-- Frozen evolution satisfies the actual right strong Schrödinger equation. -/
theorem strong_right_derivative (x : D) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (fun u => V.evolution u (domain.inclusion x))
      (z • stepHamiltonian H n t (V.lift t x)) (Ici t) t := by
  let j := gridIndex n t
  let a : ℝ := j * gridMesh n
  let y := timeOrderedProduct (fun k => (V.propagator k).lift (gridMesh n)) j x
  have hj : j < n + 1 := gridIndex_lt ht
  obtain ⟨hlo, hhi⟩ := gridIndex_bounds (n := n) ht.1
  have hprefix : timeOrderedProduct (fun k => (V.propagator k).evolution (gridMesh n)) j
      (domain.inclusion x) = domain.inclusion y := by
    exact timeOrderedProduct_preserves_domain domain.inclusion _ _
      (fun k v => (V.propagator k).preserves_domain (gridMesh n) v) j x
  have hd := ((V.propagator j).strong_derivative y (t - a)).scomp t
    ((hasDerivAt_id t).sub_const a)
  have heq : (fun u => V.evolution u (domain.inclusion x)) =ᶠ[𝓝[Ici t] t]
      (fun u => (V.propagator j).evolution (u - a) (domain.inclusion y)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hhi).filter_mono nhdsWithin_le_nhds] with u hu hu'
    rw [V.evolution_eq_cell hj (hlo.trans hu) hu'.le]
    simp only [ContinuousLinearMap.mul_apply, hprefix, a]
  have heqt : V.evolution t (domain.inclusion x) =
      (V.propagator j).evolution (t - a) (domain.inclusion y) := by
    rw [V.evolution_eq_cell hj hlo hhi.le]
    simp only [ContinuousLinearMap.mul_apply, hprefix, a]
  have hlift : V.lift t x = (V.propagator j).lift (t - a) y := by
    rw [V.lift_eq_cell hj hlo hhi.le]
    rfl
  simpa only [one_smul, stepHamiltonian, hlift] using
    hd.hasDerivWithinAt.congr_of_eventuallyEq heq heqt

end FrozenFamily
end Hilbert

/-- Reverse chronological multiplication, used for inverse evolutions. -/
def reverseTimeOrderedProduct {A : Type*} [Monoid A] (a : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => reverseTimeOrderedProduct a n * a n

@[simp] theorem reverseTimeOrderedProduct_zero {A : Type*} [Monoid A] (a : ℕ → A) :
    reverseTimeOrderedProduct a 0 = 1 := rfl

@[simp] theorem reverseTimeOrderedProduct_succ {A : Type*} [Monoid A] (a : ℕ → A) (n : ℕ) :
    reverseTimeOrderedProduct a (n + 1) = reverseTimeOrderedProduct a n * a n := rfl

namespace FrozenFamily

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {domain : CommonDomain D E} {H : ℝ → D →L[ℂ] E} {z : ℂ} {n : ℕ}
  (V : FrozenFamily domain H z n)

/-- The inverse lift applies negative-time frozen factors in reverse order. -/
def inverseLift (t : ℝ) : D →L[ℂ] D :=
  reverseTimeOrderedProduct
    (fun k => (V.propagator k).lift (-gridDuration n k t)) (n + 1)

omit [CompleteSpace D] in
omit [CompleteSpace D] in
/-- The inverse frozen evolution preserves the full common domain. -/
theorem inverse_preserves_domain (t : ℝ) (x : D) :
    star (V.evolution t) (domain.inclusion x) = domain.inclusion (V.inverseLift t x) := by
  have hprod (m : ℕ) (y : D) :
      star (timeOrderedProduct (fun k => (V.propagator k).evolution (gridDuration n k t)) m)
        (domain.inclusion y) = domain.inclusion
          (reverseTimeOrderedProduct (fun k => (V.propagator k).lift (-gridDuration n k t)) m y) := by
    induction m generalizing y with
    | zero => simp
    | succ m ih =>
      rw [timeOrderedProduct_succ, star_mul, ContinuousLinearMap.mul_apply,
        (V.propagator m).star_eq_neg, (V.propagator m).preserves_domain, ih,
        reverseTimeOrderedProduct_succ, ContinuousLinearMap.mul_apply]
  exact hprod (n + 1) x

omit [CompleteSpace D] in
/-- The forward and inverse domain lifts cancel. -/
theorem lift_inverseLift (t : ℝ) (x : D) : V.lift t (V.inverseLift t x) = x := by
  apply domain.injective
  rw [← V.preserves_domain, ← V.inverse_preserves_domain]
  exact congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
    (Unitary.mul_star_self_of_mem (V.isUnitary t))

omit [CompleteSpace D] in
/-- Cancellation also holds in the inverse-forward order. -/
theorem inverseLift_lift (t : ℝ) (x : D) : V.inverseLift t (V.lift t x) = x := by
  apply domain.injective
  rw [← V.inverse_preserves_domain, ← V.preserves_domain]
  exact congrArg (fun A : E →L[ℂ] E => A (domain.inclusion x))
    (Unitary.star_mul_self_of_mem (V.isUnitary t))

omit [CompleteSpace D] in
/-- The common-domain lift inherits the autonomous group law. -/
theorem factor_lift_add (k : ℕ) (s t : ℝ) :
    (V.propagator k).lift (s + t) = (V.propagator k).lift s * (V.propagator k).lift t := by
  ext x
  apply domain.injective
  simp only [← (V.propagator k).preserves_domain, ContinuousLinearMap.mul_apply,
    (V.propagator k).group_law]

omit [CompleteSpace D] in
/-- Frozen factors already completed at the earlier time cancel exactly. -/
theorem lift_eq_increment_mul {s t : ℝ} (hst : s ≤ t) :
    V.lift t = timeOrderedProduct
      (fun k => (V.propagator k).lift (gridDuration n k t - gridDuration n k s)) (n + 1) *
        V.lift s := by
  let A := fun k => (V.propagator k).lift (gridDuration n k t - gridDuration n k s)
  let B := fun k => (V.propagator k).lift (gridDuration n k s)
  have hcomm (k : ℕ) : B k * timeOrderedProduct A k = timeOrderedProduct A k * B k := by
    by_cases hk : gridDuration n k s = 0
    · simp only [B, hk, V.factor_lift_zero, one_mul, mul_one]
    · have hks : k * gridMesh n ≤ s := by
        by_contra h
        have hn : s - k * gridMesh n ≤ 0 := by linarith
        exact hk (by simp only [gridDuration, max_eq_right hn, min_eq_left (gridMesh_pos n).le])
      have hA : timeOrderedProduct A k = 1 := by
        have he := timeOrderedProduct_congr (a := A) (b := fun _ => 1) k (fun i hi => by
          dsimp only [A]
          rw [gridDuration_full hi hks, gridDuration_full hi (hks.trans hst), sub_self,
            V.factor_lift_zero])
        rw [he]
        clear hk hks he
        induction k with
        | zero => rfl
        | succ k ih => rw [timeOrderedProduct_succ, one_mul, ih]
      rw [hA, mul_one, one_mul]
  have hprod (m : ℕ) :
      timeOrderedProduct (fun k => (V.propagator k).lift (gridDuration n k t)) m =
        timeOrderedProduct A m * timeOrderedProduct B m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hfactor : (V.propagator m).lift (gridDuration n m t) = A m * B m := by
        dsimp only [A, B]
        rw [← V.factor_lift_add, sub_add_cancel]
      rw [timeOrderedProduct_succ, timeOrderedProduct_succ, timeOrderedProduct_succ,
        hfactor, ih]
      calc
        A m * B m * (timeOrderedProduct A m * timeOrderedProduct B m) =
            A m * (B m * timeOrderedProduct A m) * timeOrderedProduct B m := by simp only [mul_assoc]
        _ = A m * (timeOrderedProduct A m * B m) * timeOrderedProduct B m := by rw [hcomm]
        _ = _ := by simp only [mul_assoc]
  exact hprod (n + 1)

omit [CompleteSpace D] in
/-- Two-time evolution is the product of the elapsed increments. -/
theorem lift_inverseLift_eq_increment {s t : ℝ} (hst : s ≤ t) (x : D) :
    V.lift t (V.inverseLift s x) = timeOrderedProduct
      (fun k => (V.propagator k).lift (gridDuration n k t - gridDuration n k s)) (n + 1) x := by
  rw [V.lift_eq_increment_mul hst, ContinuousLinearMap.mul_apply, V.lift_inverseLift]

/-- A finite frozen family gives a right strong propagator for its
piecewise constant Hamiltonian. -/
def toRightStrongPropagator
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, domain.IsSelfAdjoint (H t)) :
    RightStrongPropagator domain (stepHamiltonian H n) z where
  evolution := V.evolution
  lift := V.lift
  inverseLift := V.inverseLift
  initial := V.initial
  isUnitary := fun t _ => V.isUnitary t
  preserves_domain := fun t _ => V.preserves_domain t
  inverse_preserves_domain := fun t _ => V.inverse_preserves_domain t
  strong_continuous := V.strong_continuous
  domain_continuous := V.domain_continuous hH
  strong_right_derivative := fun x _ ht => V.strong_right_derivative x ht

end FrozenFamily

end Adiabatic.Unbounded
