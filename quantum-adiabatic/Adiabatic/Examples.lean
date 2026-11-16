import Adiabatic.Statement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# A nontrivial two-level gapped Hamiltonian

The constant Hamiltonian `diag(0, 1)` on `ℂ²`, with the first coordinate
selected, satisfies the theorem's assumptions with gap one. The selected
projection is neither zero nor the identity, so the example checks joint
satisfiability with nonzero selected and complementary subspaces.
-/

noncomputable section

namespace Adiabatic.Examples

open Set InnerProductSpace

section ConstantProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Complementary orthogonal projections give a constant Hamiltonian with
eigenvalues zero on the selected range and one on its complement. -/
def ofProjection (P : Operator E) (hPid : P * P = P) (hPstar : star P = P) :
    GappedHamiltonian E where
  H := fun _ => 1 - P
  P := fun _ => P
  hamiltonian_smooth := contDiff_const
  projection_smooth := contDiff_const
  hamiltonian_selfAdjoint := fun _ => by simp [hPstar]
  projection_selfAdjoint := fun _ => hPstar
  projection_idempotent := fun _ => hPid
  commutes := fun _ => by noncomm_ring
  gap := 1
  spectral_gap := by
    refine ⟨zero_lt_one, ?_⟩
    intro t ht a b v w hv hw hPv hPw hHv hHw
    have hHzero : (1 - P) v = 0 := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPv, sub_self]
    have hHone : (1 - P) w = w := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPw, sub_zero]
    have haC : (a : ℂ) = 0 :=
      (smul_eq_zero.mp (hHv.symm.trans hHzero)).resolve_right hv
    have hbC : (b : ℂ) = 1 := by
      have heq : ((b : ℂ) - 1) • w = 0 := by
        rw [sub_smul, one_smul, ← hHw, hHone, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_right hw)
    have ha : a = 0 := by exact_mod_cast haC
    have hb : b = 1 := by exact_mod_cast hbC
    simp [ha, hb]

end ConstantProjection

/-- The two-dimensional complex Hilbert space with its Euclidean norm. -/
abbrev TwoLevelSpace := EuclideanSpace ℂ (Fin 2)

/-- The first standard basis vector. -/
def groundVector : TwoLevelSpace := EuclideanSpace.single 0 1

/-- The second standard basis vector. -/
def excitedVector : TwoLevelSpace := EuclideanSpace.single 1 1

/-- Orthogonal projection onto the first coordinate. -/
def groundProjection : Operator TwoLevelSpace := rankOne ℂ groundVector groundVector

lemma groundProjection_isStarProjection : IsStarProjection groundProjection := by
  apply isStarProjection_rankOne_self
  simp [groundVector]

/-- A constant Hamiltonian with energies zero and one, selecting the zero level. -/
def twoLevel : GappedHamiltonian TwoLevelSpace :=
  ofProjection groundProjection groundProjection_isStarProjection.isIdempotentElem
    groundProjection_isStarProjection.isSelfAdjoint

@[simp] theorem groundProjection_groundVector : groundProjection groundVector = groundVector := by
  simp [groundProjection, groundVector, rankOne_apply]

@[simp] theorem groundProjection_excitedVector : groundProjection excitedVector = 0 := by
  simp [groundProjection, groundVector, excitedVector, rankOne_apply,
    EuclideanSpace.inner_single_left]

theorem groundVector_ne_zero : groundVector ≠ 0 := by simp [groundVector]

theorem excitedVector_ne_zero : excitedVector ≠ 0 := by simp [excitedVector]

/-- The selected subspace is nonzero. -/
theorem groundProjection_ne_zero : groundProjection ≠ 0 := by
  intro h
  have := groundProjection_groundVector
  rw [h, ContinuousLinearMap.zero_apply] at this
  exact groundVector_ne_zero this.symm

/-- The complementary subspace is nonzero. -/
theorem groundProjection_ne_one : groundProjection ≠ 1 := by
  intro h
  have := groundProjection_excitedVector
  rw [h, ContinuousLinearMap.one_apply] at this
  exact excitedVector_ne_zero this

/-- The selected vector has energy zero for every time. -/
@[simp] theorem twoLevel_ground_energy (t : ℝ) : twoLevel.H t groundVector = 0 := by
  change (1 - groundProjection) groundVector = 0
  simp

/-- The complementary vector has energy one for every time. -/
@[simp] theorem twoLevel_excited_energy (t : ℝ) : twoLevel.H t excitedVector = excitedVector := by
  change (1 - groundProjection) excitedVector = excitedVector
  simp

/-- The example has a unit spectral gap. -/
theorem twoLevel_hasUniformSpectralGap :
    HasUniformSpectralGap TwoLevelSpace twoLevel.H twoLevel.P 1 :=
  twoLevel.spectral_gap

/-- The theorem's assumptions hold for a proper, nonzero
selected projection on a two-dimensional space. -/
theorem exists_nontrivial_gappedHamiltonian :
    ∃ data : GappedHamiltonian TwoLevelSpace, data.P 0 ≠ 0 ∧ data.P 0 ≠ 1 :=
  ⟨twoLevel, groundProjection_ne_zero, groundProjection_ne_one⟩

end Adiabatic.Examples
