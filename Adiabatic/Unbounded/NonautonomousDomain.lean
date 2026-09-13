import Adiabatic.Unbounded.Domain
import Adiabatic.Unbounded.Resolvent
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Recovery of the domain from bounded graph approximations

For a self-adjoint operator, a physical-space limit of domain vectors whose
Hamiltonian images stay bounded belongs to the domain. The proof uses the
actual maximal adjoint domain: the limiting sesquilinear form is bounded in
the physical norm and therefore defines a continuous functional. No weak
subsequence or finite-dimensional compactness is assumed.
-/

namespace Adiabatic.Unbounded.CommonDomain

open Set Filter
open scoped Topology

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (domain : CommonDomain D E) (H : D →L[ℂ] E) (hH : domain.IsSelfAdjoint H)

include hH

omit hH [CompleteSpace E] in
/-- Bounds for inner products on the dense common domain control the norm
of a physical-space vector. -/
theorem norm_le_of_inner_bound_on_domain (v : E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ y : D, ‖inner ℂ v (domain.inclusion y)‖ ≤ M * ‖domain.inclusion y‖) :
    ‖v‖ ≤ M := by
  have hall : ∀ y : E, ‖inner ℂ v y‖ ≤ M * ‖y‖ := by
    intro y
    exact domain.dense.induction_on (p := fun y => ‖inner ℂ v y‖ ≤ M * ‖y‖) y
      (isClosed_le (by fun_prop) (by fun_prop)) hbound
  have hh := hall v
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg v]

/-- A form bound on the dense common domain determines membership in the
actual self-adjoint operator domain, with the same Hamiltonian norm bound. -/
theorem exists_domain_vector_of_form_bound (v : E) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ y : D, ‖inner ℂ v (H y)‖ ≤ M * ‖domain.inclusion y‖) :
    ∃ x : D, domain.inclusion x = v ∧ ‖H x‖ ≤ M := by
  have hbounded : ∀ y : (domain.operator H).domain,
      ‖((innerₛₗ ℂ v).comp (domain.operator H).toFun) y‖ ≤ M * ‖y‖ := by
    intro y
    obtain ⟨a, rfl⟩ := domain.rangeEquiv.surjective y
    change ‖inner ℂ v (domain.operator H (domain.rangeEquiv a))‖ ≤
      M * ‖domain.inclusion a‖
    simpa using hbound a
  have hvadj : v ∈ (domain.operator H).adjoint.domain := by
    rw [(domain.operator H).mem_adjoint_domain_iff]
    exact (((innerₛₗ ℂ v).comp (domain.operator H).toFun).mkContinuous M hbounded).continuous
  have heq : (domain.operator H).adjoint = domain.operator H := hH
  have hv : v ∈ (domain.operator H).domain := by rwa [heq] at hvadj
  let x : D := domain.rangeEquiv.symm ⟨v, hv⟩
  have hx : domain.inclusion x = v := domain.inclusion_rangeEquiv_symm ⟨v, hv⟩
  refine ⟨x, hx, ?_⟩
  apply domain.norm_le_of_inner_bound_on_domain (H x) hM
  intro a
  rw [domain.inner_map H hH x a, hx]
  exact hbound a

/-- Physical convergence and a uniform bound on Hamiltonian images suffice
to recover an actual domain vector. -/
theorem exists_domain_vector_of_tendsto_of_bound
    {ι : Type*} {l : Filter ι} [l.NeBot] (x : ι → D) (v : E) {M : ℝ}
    (hM : 0 ≤ M) (hv : Tendsto (fun n => domain.inclusion (x n)) l (𝓝 v))
    (hbound : ∀ᶠ n in l, ‖H (x n)‖ ≤ M) :
    ∃ y : D, domain.inclusion y = v ∧ ‖H y‖ ≤ M := by
  apply domain.exists_domain_vector_of_form_bound H hH v hM
  intro y
  apply le_of_tendsto (hv.inner tendsto_const_nhds).norm
  filter_upwards [hbound] with n hn
  rw [← domain.inner_map H hH (x n) y]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- Sharp bounds in a shifted graph norm survive a physical-space limit
once the limit has been identified as a domain vector. -/
theorem norm_shift_le_of_tendsto_inclusion
    {ι : Type*} {l : Filter ι} [l.NeBot] (x : ι → D) (y : D) (w : ℂ) {M : ℝ}
    (hM : 0 ≤ M)
    (hv : Tendsto (fun n => domain.inclusion (x n)) l (𝓝 (domain.inclusion y)))
    (hbound : ∀ᶠ n in l, ‖domain.shift H w (x n)‖ ≤ M) :
    ‖domain.shift H w y‖ ≤ M := by
  apply domain.norm_le_of_inner_bound_on_domain (domain.shift H w y) hM
  intro a
  have hi : Tendsto (fun n => inner ℂ (domain.shift H w (x n)) (domain.inclusion a))
      l (𝓝 (inner ℂ (domain.shift H w y) (domain.inclusion a))) := by
    simpa only [shift_apply, inner_sub_left, inner_smul_left, domain.inner_map H hH] using
      (hv.inner (tendsto_const_nhds (x := H a))).sub
        ((hv.inner (tendsto_const_nhds (x := domain.inclusion a))).const_mul (star w))
  apply le_of_tendsto hi.norm
  filter_upwards [hbound] with n hn
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- Shifted graph bounds recover both domain membership and the same sharp
graph bound. The physical-space bound is used only for existence. -/
theorem exists_domain_vector_of_tendsto_of_shift_bound
    {ι : Type*} {l : Filter ι} [l.NeBot] (x : ι → D) (v : E) (w : ℂ) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hv : Tendsto (fun n => domain.inclusion (x n)) l (𝓝 v))
    (hphysical : ∀ᶠ n in l, ‖domain.inclusion (x n)‖ ≤ N)
    (hbound : ∀ᶠ n in l, ‖domain.shift H w (x n)‖ ≤ M) :
    ∃ y : D, domain.inclusion y = v ∧ ‖domain.shift H w y‖ ≤ M := by
  have hHbound : ∀ᶠ n in l, ‖H (x n)‖ ≤ M + ‖w‖ * N := by
    filter_upwards [hphysical, hbound] with n hn hb
    have heq : H (x n) = domain.shift H w (x n) + w • domain.inclusion (x n) := by simp
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hb (by rw [norm_smul]; gcongr))
  obtain ⟨y, hy, _⟩ := domain.exists_domain_vector_of_tendsto_of_bound H hH x v
    (show 0 ≤ M + ‖w‖ * N by positivity) hv hHbound
  exact ⟨y, hy, domain.norm_shift_le_of_tendsto_inclusion H hH x y w hM (by rwa [hy]) hbound⟩

end Adiabatic.Unbounded.CommonDomain
