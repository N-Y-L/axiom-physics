import Adiabatic.Unbounded.Domain
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Nonreal resolvents of self-adjoint common-domain operators

The nonreal resolvent is constructed from unbounded self-adjointness. It is a
bounded map into the common Banach domain, not merely into the physical space.
-/

noncomputable section

namespace Adiabatic.Unbounded.CommonDomain

open Set ComplexConjugate

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)

/-- The resolvent pencil acts from the common domain into the Hilbert space. -/
def shift (z : ℂ) : D →L[ℂ] E := H - z • domain.inclusion

omit [CompleteSpace E] in
@[simp] theorem shift_apply (z : ℂ) (x : D) :
    domain.shift H z x = H x - z • domain.inclusion x := rfl

include hH

/-- The expectation of a self-adjoint domain operator is real. -/
theorem inner_map_self_im (x : D) : (inner ℂ (H x) (domain.inclusion x)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [inner_conj_symm]
  exact (domain.inner_map H hH x x).symm

/-- The imaginary part gives the lower resolvent bound in the physical norm. -/
theorem norm_shift_lower (z : ℂ) (x : D) :
    |z.im| * ‖domain.inclusion x‖ ≤ ‖domain.shift H z x‖ := by
  have him : (inner ℂ (domain.shift H z x) (domain.inclusion x)).im =
      z.im * ‖domain.inclusion x‖ ^ 2 := by
    simp only [shift_apply, inner_sub_left, inner_smul_left, Complex.sub_im,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]
    rw [domain.inner_map_self_im H hH x,
      show (inner ℂ (domain.inclusion x) (domain.inclusion x)).im = 0 from
        inner_self_im (𝕜 := ℂ) _,
      show (inner ℂ (domain.inclusion x) (domain.inclusion x)).re = ‖domain.inclusion x‖ ^ 2 from
        inner_self_eq_norm_sq (𝕜 := ℂ) _]
    ring
  have hn := (Complex.abs_im_le_norm
    (inner ℂ (domain.shift H z x) (domain.inclusion x))).trans
      (norm_inner_le_norm _ _)
  rw [him, abs_mul] at hn
  rw [abs_of_nonneg (sq_nonneg ‖domain.inclusion x‖)] at hn
  by_cases hx : domain.inclusion x = 0
  · simp [hx]
  · have hpos := norm_pos_iff.mpr hx
    nlinarith

/-- A nonreal resolvent pencil is injective. -/
theorem shift_injective (z : ℂ) (hz : z.im ≠ 0) :
    Function.Injective (domain.shift H z) := by
  apply (domain.shift H z).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  change domain.shift H z x = 0 at hx
  have h := domain.norm_shift_lower H hH z x
  rw [hx, norm_zero] at h
  have hj : domain.inclusion x = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (domain.inclusion x), abs_pos.mpr hz]
  apply domain.injective
  simpa using hj

variable [CompleteSpace D]

/-- The nonreal lower bound also controls the full common-domain norm. -/
theorem norm_le_shift (z : ℂ) (hz : z.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : D, ‖x‖ ≤ C * ‖domain.shift H z x‖ := by
  obtain ⟨C, hC, hbound⟩ := domain.norm_le_graph H hH
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  refine ⟨C * (|z.im|⁻¹ + 1 + ‖z‖ * |z.im|⁻¹), by positivity, ?_⟩
  intro x
  have hj : ‖domain.inclusion x‖ ≤ |z.im|⁻¹ * ‖domain.shift H z x‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hzpos).mpr (by
      simpa only [mul_comm] using domain.norm_shift_lower H hH z x)
  have hHx : ‖H x‖ ≤ ‖domain.shift H z x‖ + ‖z‖ * ‖domain.inclusion x‖ := by
    have heq : H x = domain.shift H z x + z • domain.inclusion x := by
      simp
    calc
      ‖H x‖ = ‖domain.shift H z x + z • domain.inclusion x‖ := congrArg norm heq
      _ ≤ ‖domain.shift H z x‖ + ‖z • domain.inclusion x‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul]
  calc
    ‖x‖ ≤ C * (‖domain.inclusion x‖ + ‖H x‖) := hbound x
    _ ≤ C * (|z.im|⁻¹ * ‖domain.shift H z x‖ +
        (‖domain.shift H z x‖ + ‖z‖ * (|z.im|⁻¹ * ‖domain.shift H z x‖))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add hj
      exact hHx.trans (by gcongr)
    _ = _ := by ring

/-- The nonreal resolvent pencil has closed range. -/
theorem shift_closed_range (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed (Set.range (domain.shift H z)) := by
  obtain ⟨C, hC, hb⟩ := domain.norm_le_shift H hH z hz
  have ha : AntilipschitzWith ⟨C, hC⟩ (domain.shift H z) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simpa only [dist_eq_norm, map_sub] using hb (x - y)
  exact ha.isClosed_range (domain.shift H z).uniformContinuous

omit [CompleteSpace D] in
/-- A vector orthogonal to the shifted range must vanish. -/
theorem shift_range_orthogonal_eq_bot (z : ℂ) (hz : z.im ≠ 0) :
    (domain.shift H z).rangeᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  change y = 0
  have hyinner : ∀ x : D,
      inner ℂ (conj z • y) (domain.inclusion x) = inner ℂ y (H x) := by
    intro x
    have h := (Submodule.mem_orthogonal' (domain.shift H z).range y).mp hy
      (domain.shift H z x) ((domain.shift H z).mem_range_self x)
    simp only [shift_apply, inner_sub_right, inner_smul_right] at h
    simpa only [inner_smul_left, starRingEnd_self_apply] using (sub_eq_zero.mp h).symm
  have hya : ∀ x : (domain.operator H).domain,
      inner ℂ (conj z • y) (x : E) = inner ℂ y (domain.operator H x) := by
    intro x
    obtain ⟨v, rfl⟩ := domain.rangeEquiv.surjective x
    simpa using hyinner v
  have hyadj := (domain.operator H).mem_adjoint_domain_of_exists y ⟨conj z • y, hya⟩
  have hadj : (domain.operator H).adjoint = domain.operator H := hH
  have hyD : y ∈ (domain.operator H).domain := by
    rw [← hadj]
    exact hyadj
  let x : D := domain.rangeEquiv.symm ⟨y, hyD⟩
  have hjx : domain.inclusion x = y := domain.inclusion_rangeEquiv_symm ⟨y, hyD⟩
  have hHx : H x = conj z • y := by
    have h := (domain.operator H).adjoint_apply_eq
      (show Dense ((domain.operator H).domain : Set E) from domain.dense)
      ⟨y, hyadj⟩ hya
    have heval := (LinearPMap.ext_iff.mp hadj).2 (x := y) (hf := hyadj) (hg := hyD)
    exact heval.symm.trans h
  have hx : domain.shift H (conj z) x = 0 := by simp [hjx, hHx]
  have hz' : (conj z).im ≠ 0 := by simpa using hz
  have hx0 : x = 0 := domain.shift_injective H hH (conj z) hz' (by simpa using hx)
  simpa [hx0] using hjx.symm

/-- Every nonreal point is in the resolvent set of a self-adjoint operator. -/
theorem shift_bijective (z : ℂ) (hz : z.im ≠ 0) :
    Function.Bijective (domain.shift H z) := by
  refine ⟨domain.shift_injective H hH z hz, ?_⟩
  have hc : (domain.shift H z).range.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff).mpr
      (domain.shift_range_orthogonal_eq_bot H hH z hz)
  have hclosed : IsClosed ((domain.shift H z).range : Set E) :=
    domain.shift_closed_range H hH z hz
  rw [hclosed.submodule_topologicalClosure_eq] at hc
  exact LinearMap.range_eq_top.mp hc

/-- The nonreal resolvent pencil, as a continuous linear equivalence. -/
def resolventEquiv (z : ℂ) (hz : z.im ≠ 0) : D ≃L[ℂ] E :=
  (LinearEquiv.ofBijective (domain.shift H z).toLinearMap
    (domain.shift_bijective H hH z hz)).toContinuousLinearEquivOfContinuous
      (domain.shift H z).continuous

/-- The nonreal resolvent maps boundedly into the full common domain. -/
def resolvent (z : ℂ) (hz : z.im ≠ 0) : E →L[ℂ] D :=
  (domain.resolventEquiv H hH z hz).symm.toContinuousLinearMap

@[simp] theorem shift_resolvent (z : ℂ) (hz : z.im ≠ 0) (x : E) :
    domain.shift H z (domain.resolvent H hH z hz x) = x :=
  (domain.resolventEquiv H hH z hz).apply_symm_apply x

@[simp] theorem resolvent_shift (z : ℂ) (hz : z.im ≠ 0) (x : D) :
    domain.resolvent H hH z hz (domain.shift H z x) = x :=
  (domain.resolventEquiv H hH z hz).symm_apply_apply x

/-- The usual physical-space resolvent bound. -/
theorem norm_inclusion_resolvent_le (z : ℂ) (hz : z.im ≠ 0) (x : E) :
    ‖domain.inclusion (domain.resolvent H hH z hz x)‖ ≤ ‖x‖ / |z.im| := by
  apply (le_div_iff₀ (abs_pos.mpr hz)).mpr
  simpa only [shift_resolvent, mul_comm] using
    domain.norm_shift_lower H hH z (domain.resolvent H hH z hz x)

/-- The resolvent acting on the physical Hilbert space. -/
def physicalResolvent (z : ℂ) (hz : z.im ≠ 0) : E →L[ℂ] E :=
  domain.inclusion.comp (domain.resolvent H hH z hz)

@[simp] theorem physicalResolvent_apply (z : ℂ) (hz : z.im ≠ 0) (x : E) :
    domain.physicalResolvent H hH z hz x =
      domain.inclusion (domain.resolvent H hH z hz x) := rfl

/-- Applying the Hamiltonian to its resolvent. -/
theorem map_resolvent (z : ℂ) (hz : z.im ≠ 0) (x : E) :
    H (domain.resolvent H hH z hz x) = x + z • domain.physicalResolvent H hH z hz x := by
  have h := domain.shift_resolvent H hH z hz x
  rw [shift_apply] at h
  exact sub_eq_iff_eq_add.mp h

/-- Applying the resolvent to the Hamiltonian on its domain. -/
theorem resolvent_map (z : ℂ) (hz : z.im ≠ 0) (x : D) :
    domain.resolvent H hH z hz (H x) =
      x + z • domain.resolvent H hH z hz (domain.inclusion x) := by
  have h := domain.resolvent_shift H hH z hz x
  rw [shift_apply, map_sub, map_smul] at h
  exact sub_eq_iff_eq_add.mp h

/-- The first resolvent identity, with values in the common domain. -/
theorem resolvent_sub (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : E) :
    domain.resolvent H hH z hz x - domain.resolvent H hH w hw x =
      (z - w) • domain.resolvent H hH z hz
        (domain.physicalResolvent H hH w hw x) := by
  apply domain.shift_injective H hH z hz
  simp only [map_sub, map_smul, shift_resolvent]
  rw [shift_apply, domain.map_resolvent H hH w hw]
  simp only [physicalResolvent_apply]
  module

/-- The physical first resolvent identity. -/
theorem physicalResolvent_sub (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    domain.physicalResolvent H hH z hz - domain.physicalResolvent H hH w hw =
      (z - w) • (domain.physicalResolvent H hH z hz *
        domain.physicalResolvent H hH w hw) := by
  ext x
  have h := congrArg domain.inclusion (domain.resolvent_sub H hH z w hz hw x)
  simpa using h

/-- Resolvents of the same unbounded self-adjoint operator commute. -/
theorem physicalResolvent_commute (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Commute (domain.physicalResolvent H hH z hz) (domain.physicalResolvent H hH w hw) := by
  by_cases hzw : z = w
  · subst w
    exact Commute.refl _
  have h₁ := domain.physicalResolvent_sub H hH z w hz hw
  have h₂ := domain.physicalResolvent_sub H hH w z hw hz
  apply (smul_right_injective _ (sub_ne_zero.mpr hzw))
  change (z - w) • (domain.physicalResolvent H hH z hz * domain.physicalResolvent H hH w hw) =
    (z - w) • (domain.physicalResolvent H hH w hw * domain.physicalResolvent H hH z hz)
  rw [← h₁, ← neg_sub w z, neg_smul, ← h₂, neg_sub]

/-- Conjugating the spectral parameter takes the Hilbert-space adjoint. -/
theorem physicalResolvent_star (z : ℂ) (hz : z.im ≠ 0) :
    star (domain.physicalResolvent H hH z hz) =
      domain.physicalResolvent H hH (conj z) (by simpa using hz) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  let u := domain.resolvent H hH (conj z) (by simpa using hz) x
  let v := domain.resolvent H hH z hz y
  have hu : domain.shift H (conj z) u = x := domain.shift_resolvent H hH _ _ x
  have hv : domain.shift H z v = y := domain.shift_resolvent H hH _ _ y
  change inner ℂ (domain.inclusion u) y = inner ℂ x (domain.inclusion v)
  rw [← hu, ← hv]
  simp only [shift_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_self_apply]
  rw [domain.inner_map H hH u v]

/-- Resolvent regularization approaches the identity on the common domain. -/
theorem norm_regularization_sub_le (z : ℂ) (hz : z.im ≠ 0) (x : D) :
    ‖(-z) • domain.physicalResolvent H hH z hz (domain.inclusion x) - domain.inclusion x‖ ≤
      ‖H x‖ / |z.im| := by
  have h := congrArg domain.inclusion (domain.resolvent_map H hH z hz x)
  simp only [map_add, map_smul] at h
  have heq : (-z) • domain.physicalResolvent H hH z hz (domain.inclusion x) -
      domain.inclusion x = -domain.physicalResolvent H hH z hz (H x) := by
    change (-z) • domain.inclusion (domain.resolvent H hH z hz (domain.inclusion x)) -
      domain.inclusion x = -domain.inclusion (domain.resolvent H hH z hz (H x))
    rw [h]
    module
  rw [heq, norm_neg]
  exact domain.norm_inclusion_resolvent_le H hH z hz (H x)

omit hH

/-- The actual resolvent set, using bijectivity on the full common domain. -/
def resolventSet : Set ℂ := {z | Function.Bijective (domain.shift H z)}

/-- The unbounded spectrum is the complement of the resolvent set. -/
def spectrum : Set ℂ := (domain.resolventSet H)ᶜ

include hH in
/-- Every nonreal complex number belongs to the resolvent set. -/
theorem mem_resolventSet_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ domain.resolventSet H := domain.shift_bijective H hH z hz

include hH in
/-- The spectrum of the genuine unbounded self-adjoint operator is real. -/
theorem spectrum_im_eq_zero {z : ℂ} (hz : z ∈ domain.spectrum H) : z.im = 0 := by
  by_contra h
  exact hz (domain.mem_resolventSet_of_im_ne_zero H hH z h)

/-- The inverse at any resolvent point, including real spectral-gap points. -/
def resolventAtEquiv (z : ℂ) (hz : z ∈ domain.resolventSet H) : D ≃L[ℂ] E :=
  (LinearEquiv.ofBijective (domain.shift H z).toLinearMap hz).toContinuousLinearEquivOfContinuous
    (domain.shift H z).continuous

/-- A total inverse function, with zero at noninvertible pencils, for calculus. -/
def inverseShift (z : ℂ) : E →L[ℂ] D := (domain.shift H z).inverse

/-- On the actual resolvent set, the total inverse is the genuine inverse. -/
theorem inverseShift_eq (z : ℂ) (hz : z ∈ domain.resolventSet H) :
    domain.inverseShift H z = (domain.resolventAtEquiv H z hz).symm.toContinuousLinearMap :=
  ContinuousLinearMap.inverse_equiv (domain.resolventAtEquiv H z hz)

include hH in
/-- Agreement between the total inverse and the constructed nonreal resolvent. -/
theorem inverseShift_eq_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    domain.inverseShift H z = domain.resolvent H hH z hz :=
  ContinuousLinearMap.inverse_equiv (domain.resolventEquiv H hH z hz)

@[simp] theorem shift_inverseShift (z : ℂ) (hz : z ∈ domain.resolventSet H) (x : E) :
    domain.shift H z (domain.inverseShift H z x) = x := by
  rw [domain.inverseShift_eq H z hz]
  exact (domain.resolventAtEquiv H z hz).apply_symm_apply x

@[simp] theorem inverseShift_shift (z : ℂ) (hz : z ∈ domain.resolventSet H) (x : D) :
    domain.inverseShift H z (domain.shift H z x) = x := by
  rw [domain.inverseShift_eq H z hz]
  exact (domain.resolventAtEquiv H z hz).symm_apply_apply x

/-- The total physical resolvent, suitable for spectral integration. -/
def physicalInverseShift (z : ℂ) : E →L[ℂ] E := domain.inclusion.comp (domain.inverseShift H z)

omit [CompleteSpace E] [CompleteSpace D] in
@[simp] theorem physicalInverseShift_apply (z : ℂ) (x : E) :
    domain.physicalInverseShift H z x = domain.inclusion (domain.inverseShift H z x) := rfl

include hH in
@[simp] theorem physicalInverseShift_eq_physicalResolvent (z : ℂ) (hz : z.im ≠ 0) :
    domain.physicalInverseShift H z = domain.physicalResolvent H hH z hz := by
  simp only [physicalInverseShift, inverseShift_eq_resolvent domain H hH z hz, physicalResolvent]

theorem map_inverseShift (z : ℂ) (hz : z ∈ domain.resolventSet H) (x : E) :
    H (domain.inverseShift H z x) = x + z • domain.physicalInverseShift H z x := by
  have h := domain.shift_inverseShift H z hz x
  rw [shift_apply] at h
  exact sub_eq_iff_eq_add.mp h

theorem inverseShift_map (z : ℂ) (hz : z ∈ domain.resolventSet H) (x : D) :
    domain.inverseShift H z (H x) = x + z • domain.inverseShift H z (domain.inclusion x) := by
  have h := domain.inverseShift_shift H z hz x
  rw [shift_apply, map_sub, map_smul] at h
  exact sub_eq_iff_eq_add.mp h

/-- The physical resolvent commutes with the Hamiltonian on its full domain. -/
theorem map_inverseShift_inclusion (z : ℂ) (hz : z ∈ domain.resolventSet H) (x : D) :
    H (domain.inverseShift H z (domain.inclusion x)) = domain.physicalInverseShift H z (H x) := by
  rw [domain.map_inverseShift H z hz]
  have h := congrArg domain.inclusion (domain.inverseShift_map H z hz x)
  simpa only [map_add, map_smul] using h.symm

/-- The domain commutator of a resolvent sandwich is a bounded resolvent difference. -/
theorem inverseShift_sandwich_commutator (B : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ domain.resolventSet H) (x : D) :
    H (domain.inverseShift H z (B (domain.physicalInverseShift H z (domain.inclusion x)))) -
      domain.physicalInverseShift H z (B (domain.physicalInverseShift H z (H x))) =
        B (domain.physicalInverseShift H z (domain.inclusion x)) -
          domain.physicalInverseShift H z (B (domain.inclusion x)) := by
  have h := congrArg domain.inclusion (domain.inverseShift_map H z hz x)
  simp only [map_add, map_smul] at h
  change domain.physicalInverseShift H z (H x) = domain.inclusion x +
    z • domain.physicalInverseShift H z (domain.inclusion x) at h
  rw [domain.map_inverseShift H z hz, h]
  simp only [map_add, map_smul]
  module

/-- The resolvent identity applies also at real spectral-gap points. -/
theorem inverseShift_sub (z w : ℂ) (hz : z ∈ domain.resolventSet H)
    (hw : w ∈ domain.resolventSet H) (x : E) :
    domain.inverseShift H z x - domain.inverseShift H w x =
      (z - w) • domain.inverseShift H z (domain.physicalInverseShift H w x) := by
  apply hz.1
  simp only [map_sub, map_smul, shift_inverseShift domain H z hz]
  rw [shift_apply, domain.map_inverseShift H w hw]
  simp only [physicalInverseShift_apply]
  module

/-- The physical resolvent identity on the full resolvent set. -/
theorem physicalInverseShift_sub (z w : ℂ) (hz : z ∈ domain.resolventSet H)
    (hw : w ∈ domain.resolventSet H) :
    domain.physicalInverseShift H z - domain.physicalInverseShift H w =
      (z - w) • (domain.physicalInverseShift H z * domain.physicalInverseShift H w) := by
  ext x
  simpa using congrArg domain.inclusion (domain.inverseShift_sub H z w hz hw x)

/-- Bijective bounded maps between Banach spaces form an open set. -/
theorem isOpen_setOf_bijective : IsOpen {f : D →L[ℂ] E | Function.Bijective f} := by
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  let e : D ≃L[ℂ] E := (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuous
    f.continuous
  have hc : Continuous (fun g : D →L[ℂ] E => e.symm.toContinuousLinearMap.comp g) := by
    fun_prop
  have he : e.symm.toContinuousLinearMap.comp f = 1 := by
    ext x
    exact e.symm_apply_apply x
  have hu : IsUnit (e.symm.toContinuousLinearMap.comp f) := by rw [he]; exact isUnit_one
  have hnear := hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hu)
  filter_upwards [hnear] with g hg
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hg
  exact (e.symm.bijective.of_comp_iff' g).mp hb

/-- The resolvent set of a closed common-domain operator is open. -/
theorem isOpen_resolventSet : IsOpen (domain.resolventSet H) := by
  exact isOpen_setOf_bijective.preimage (by
    unfold shift
    fun_prop)

/-- The actual unbounded spectrum is closed. -/
theorem isClosed_spectrum : IsClosed (domain.spectrum H) :=
  (domain.isOpen_resolventSet H).isClosed_compl

/-- Smooth dependence of the resolvent on the domain operator. -/
theorem inverseShift_contDiffAt_operator (z : ℂ) (hz : z ∈ domain.resolventSet H)
    (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (fun K : D →L[ℂ] E => domain.inverseShift K z) H := by
  have hi : ContDiffAt ℂ n ContinuousLinearMap.inverse (domain.shift H z) :=
    contDiffAt_map_inverse (domain.resolventAtEquiv H z hz)
  exact hi.comp H (contDiffAt_id.sub contDiffAt_const)

/-- Holomorphic smoothness of the resolvent in the spectral parameter. -/
theorem inverseShift_contDiffAt_parameter (z : ℂ) (hz : z ∈ domain.resolventSet H)
    (n : WithTop ℕ∞) : ContDiffAt ℂ n (domain.inverseShift H) z := by
  have hi : ContDiffAt ℂ n ContinuousLinearMap.inverse (domain.shift H z) :=
    contDiffAt_map_inverse (domain.resolventAtEquiv H z hz)
  exact hi.comp z (contDiffAt_const.sub (contDiffAt_id.smul contDiffAt_const))

section RealParameter

variable [NormedSpace ℝ D] [IsScalarTower ℝ ℂ D]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- A smooth common-domain Hamiltonian has a smooth resolvent near each regular point. -/
theorem inverseShift_contDiffAt_path (A : ℝ → D →L[ℂ] E) (t : ℝ) (z : ℂ)
    (hz : z ∈ domain.resolventSet (A t)) (n : WithTop ℕ∞) (hA : ContDiffAt ℝ n A t) :
    ContDiffAt ℝ n (fun s => domain.inverseShift (A s) z) t :=
  ((domain.inverseShift_contDiffAt_operator (A t) z hz n).restrict_scalars ℝ).comp t hA

end RealParameter

end Adiabatic.Unbounded.CommonDomain
