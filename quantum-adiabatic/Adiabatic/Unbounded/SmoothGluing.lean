import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smoothly gluing local solutions of linear equations

A finite smooth partition of unity on a compact real set combines local
solutions of a time-dependent linear equation. The local solutions need
only be smooth within the compact set, so interval endpoints require no
extension of the original data.
-/

noncomputable section

namespace Adiabatic.Unbounded

open Set Function Filter
open scoped Topology Manifold

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Local `C¹` solutions of linear equations glue over a compact subset of the real line. -/
theorem exists_contDiffOn_linear_solution {s : Set ℝ} (hs : IsCompact s)
    (T : ℝ → V →ₗ[ℝ] W) (b : ℝ → W)
    (hlocal : ∀ x ∈ s, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ∃ g : ℝ → V, ContDiffOn ℝ 1 g (s ∩ U) ∧ ∀ t ∈ s ∩ U, T t (g t) = b t) :
    ∃ g : ℝ → V, ContDiffOn ℝ 1 g s ∧ ∀ t ∈ s, T t (g t) = b t := by
  classical
  have hl (x : s) := hlocal x x.property
  choose U hUo hxU g hg heq using hl
  have hcover : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨J, hJ⟩ := hs.elim_finite_subcover U hUo hcover
  have hcoverJ : s ⊆ ⋃ i : J, U i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ) hs.isClosed
    (fun i : J => U i.val) (fun i => hUo i.val) hcoverJ
  refine ⟨fun x => ∑ i : J, ρ i x • g i.val x, ?_, ?_⟩
  · intro x hx
    apply ContDiffWithinAt.sum
    intro i _
    by_cases hi : x ∈ tsupport (ρ i)
    · have hu : U i.val ∈ 𝓝 x := (hUo i.val).mem_nhds (hρ i hi)
      have hgi : ContDiffWithinAt ℝ 1 (g i.val) s x :=
        (contDiffWithinAt_inter hu).mp (hg i.val x ⟨hx, hρ i hi⟩)
      have hρi : ContDiff ℝ 1 (ρ i : ℝ → ℝ) :=
        (contMDiff_iff_contDiff.mp (ρ i).contMDiff).of_le (by norm_num)
      exact hρi.contDiffWithinAt.smul hgi
    · have hzero : (fun t => ρ i t • g i.val t) =ᶠ[𝓝 x] fun _ => (0 : V) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hi] with t ht
        simp only [ht, Pi.zero_apply, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt
  · intro t ht
    rw [map_sum]
    have hterm (i : J) : T t (ρ i t • g i.val t) = ρ i t • b t := by
      rw [map_smul]
      by_cases hz : ρ i t = 0
      · simp [hz]
      · rw [heq i.val t ⟨ht, hρ i (subset_closure hz)⟩]
    simp_rw [hterm]
    rw [← Finset.sum_smul]
    have hsum : ∑ i : J, ρ i t = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one ht
    rw [hsum, one_smul]

end Adiabatic.Unbounded
