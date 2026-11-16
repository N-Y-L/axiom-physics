import Adiabatic.Projection
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Inverting the commutator across a spectral gap

The fixed-space superoperator is the identity on diagonal blocks and the Hamiltonian
commutator on off-diagonal blocks. Its injectivity follows from spectral separation.
The proof uses a single eigenbasis of the Hamiltonian at one time; it makes no choices
of differentiable eigenvectors.
-/

noncomputable section

namespace Adiabatic

section Superoperator

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Retain the two diagonal blocks relative to an idempotent. -/
def diagonalSuperoperator (P : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mulLeftRight ℂ A P P +
    ContinuousLinearMap.mulLeftRight ℂ A (1 - P) (1 - P)

/-- Retain the two off-diagonal blocks relative to an idempotent. -/
def offDiagonalSuperoperator (P : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mulLeftRight ℂ A P (1 - P) +
    ContinuousLinearMap.mulLeftRight ℂ A (1 - P) P

/-- Identity on diagonal blocks, and Hamiltonian commutator on off-diagonal blocks. -/
def gapSuperoperator (H P : A) : A →L[ℂ] A :=
  diagonalSuperoperator P +
    (ContinuousLinearMap.mul ℂ A H - (ContinuousLinearMap.mul ℂ A).flip H).comp
      (offDiagonalSuperoperator P)

@[simp] theorem diagonalSuperoperator_apply (P X : A) :
    diagonalSuperoperator P X = P * X * P + (1 - P) * X * (1 - P) := rfl

@[simp] theorem offDiagonalSuperoperator_apply (P X : A) :
    offDiagonalSuperoperator P X = P * X * (1 - P) + (1 - P) * X * P := rfl

@[simp] theorem gapSuperoperator_apply (H P X : A) :
    gapSuperoperator H P X = diagonalSuperoperator P X +
      (H * offDiagonalSuperoperator P X - offDiagonalSuperoperator P X * H) := rfl

/-- Every operator is the sum of its diagonal and off-diagonal blocks. -/
theorem diagonal_add_offDiagonal (P X : A) :
    diagonalSuperoperator P X + offDiagonalSuperoperator P X = X := by
  simp only [diagonalSuperoperator_apply, offDiagonalSuperoperator_apply]
  noncomm_ring

/-- Compressing the gap superoperator to the selected block returns that block. -/
theorem gapSuperoperator_sandwich {H P : A} (hP : P * P = P)
    (hHP : H * P = P * H) (X : A) :
    P * gapSuperoperator H P X * P = P * X * P := by
  have hPP (Y : A) : P * (P * Y) = P * Y := by rw [← mul_assoc, hP]
  have hHPY (Y : A) : H * (P * Y) = P * (H * Y) := by rw [← mul_assoc, hHP, mul_assoc]
  simp only [gapSuperoperator_apply, diagonalSuperoperator_apply, offDiagonalSuperoperator_apply]
  noncomm_ring [hPP, hHPY, hP, hHP]

/-- Compressing the gap superoperator to the complementary block returns that block. -/
theorem gapSuperoperator_complement_sandwich {H P : A} (hP : P * P = P)
    (hHP : H * P = P * H) (X : A) :
    (1 - P) * gapSuperoperator H P X * (1 - P) = (1 - P) * X * (1 - P) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP]
  have hHQ : H * (1 - P) = (1 - P) * H := by noncomm_ring [hHP]
  have hsame : gapSuperoperator H (1 - P) X = gapSuperoperator H P X := by
    simp only [gapSuperoperator_apply, diagonalSuperoperator_apply, offDiagonalSuperoperator_apply]
    noncomm_ring
  simpa only [hsame] using gapSuperoperator_sandwich hQ hHQ X

/-- A vector in the kernel has zero diagonal blocks and commutes with the Hamiltonian. -/
theorem gapSuperoperator_kernel {H P X : A} (hP : P * P = P)
    (hHP : H * P = P * H) (hX : gapSuperoperator H P X = 0) :
    P * X * P = 0 ∧ (1 - P) * X * (1 - P) = 0 ∧ H * X = X * H := by
  have hPX : P * X * P = 0 := by
    rw [← gapSuperoperator_sandwich hP hHP X, hX, mul_zero, zero_mul]
  have hQX : (1 - P) * X * (1 - P) = 0 := by
    rw [← gapSuperoperator_complement_sandwich hP hHP X, hX, mul_zero, zero_mul]
  have hd : diagonalSuperoperator P X = 0 := by simp [hPX, hQX]
  have ho : offDiagonalSuperoperator P X = X := by
    simpa only [hd, zero_add] using diagonal_add_offDiagonal P X
  refine ⟨hPX, hQX, ?_⟩
  simpa only [gapSuperoperator_apply, hd, ho, zero_add, sub_eq_zero] using hX

/-- The commutator solution obtained by inversion on the fixed operator space. -/
def commutatorSolution (H P K : A) : A :=
  Ring.inverse (gapSuperoperator H P) K

/-- Inverting the gap superoperator solves the commutator equation for off-diagonal data. -/
theorem commutatorSolution_commutator {H P K : A} (hP : P * P = P)
    (hHP : H * P = P * H) (hunit : IsUnit (gapSuperoperator H P))
    (hPK : P * K * P = 0) (hQK : (1 - P) * K * (1 - P) = 0) :
    H * commutatorSolution H P K - commutatorSolution H P K * H = K := by
  have hLX : gapSuperoperator H P (commutatorSolution H P K) = K :=
    DFunLike.congr_fun (Ring.mul_inverse_cancel (gapSuperoperator H P) hunit) K
  have hPX : P * commutatorSolution H P K * P = 0 := by
    rw [← gapSuperoperator_sandwich hP hHP, hLX, hPK]
  have hQX : (1 - P) * commutatorSolution H P K * (1 - P) = 0 := by
    rw [← gapSuperoperator_complement_sandwich hP hHP, hLX, hQK]
  have hd : diagonalSuperoperator P (commutatorSolution H P K) = 0 := by simp [hPX, hQX]
  have ho : offDiagonalSuperoperator P (commutatorSolution H P K) =
      commutatorSolution H P K := by
    simpa only [hd, zero_add] using diagonal_add_offDiagonal P (commutatorSolution H P K)
  simpa only [gapSuperoperator_apply, hd, ho, zero_add] using hLX

omit [NormedAlgebra ℂ A] in
/-- Kato's generator is always off-diagonal relative to its idempotent. -/
theorem katoGenerator_diagonal_blocks {P : A} (hP : P * P = P) (dP : A) :
    P * katoGenerator P dP * P = 0 ∧
      (1 - P) * katoGenerator P dP * (1 - P) = 0 := by
  have hPP (Y : A) : P * (P * Y) = P * Y := by rw [← mul_assoc, hP]
  constructor <;> unfold katoGenerator <;> noncomm_ring [hPP, hP]

/-- The inverse superoperator solves the commutator equation required by Kato transport. -/
theorem commutatorSolution_katoGenerator {H P : A} (hP : P * P = P)
    (hHP : H * P = P * H) (hunit : IsUnit (gapSuperoperator H P)) (dP : A) :
    H * commutatorSolution H P (katoGenerator P dP) -
      commutatorSolution H P (katoGenerator P dP) * H = katoGenerator P dP := by
  obtain ⟨hPK, hQK⟩ := katoGenerator_diagonal_blocks hP dP
  exact commutatorSolution_commutator hP hHP hunit hPK hQK

end Superoperator

section SpectralSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The selected and complementary sectors have no common real eigenvalue. -/
def HasDisjointSectorEigenvalues (H P : E →L[ℂ] E) : Prop :=
  ∀ (a : ℝ) (v w : E), v ≠ 0 → w ≠ 0 → P v = v → P w = 0 →
    H v = (a : ℂ) • v → H w = (a : ℂ) • w → False

/-- Spectral separation kills an off-diagonal intertwiner on each eigenvector. -/
theorem offDiagonal_commuting_kills_eigenvector {H P X : E →L[ℂ] E}
    (hP : P * P = P) (hHP : H * P = P * H) (hHX : H * X = X * H)
    (hPX : P * X * P = 0) (hQX : (1 - P) * X * (1 - P) = 0)
    (hgap : HasDisjointSectorEigenvalues H P) {a : ℝ} {v : E}
    (hv : H v = (a : ℂ) • v) : X v = 0 := by
  have hPP : P (P v) = P v := DFunLike.congr_fun hP v
  have hpv : H (P v) = (a : ℂ) • P v := by
    calc
      H (P v) = P (H v) := DFunLike.congr_fun hHP v
      _ = (a : ℂ) • P v := by rw [hv, map_smul]
  have hxpv : H (X (P v)) = (a : ℂ) • X (P v) := by
    calc
      H (X (P v)) = X (H (P v)) := DFunLike.congr_fun hHX (P v)
      _ = (a : ℂ) • X (P v) := by rw [hpv, map_smul]
  have hxp : X (P v) = 0 := by
    by_contra hx
    have hp : P v ≠ 0 := fun hp => hx (by rw [hp, map_zero])
    exact hgap a (P v) (X (P v)) hp hx hPP (DFunLike.congr_fun hPX v) hpv hxpv
  have hqv : H ((1 - P) v) = (a : ℂ) • (1 - P) v := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub, hv, hpv, smul_sub]
  have hxqv : H (X ((1 - P) v)) = (a : ℂ) • X ((1 - P) v) := by
    calc
      H (X ((1 - P) v)) = X (H ((1 - P) v)) := DFunLike.congr_fun hHX ((1 - P) v)
      _ = (a : ℂ) • X ((1 - P) v) := by rw [hqv, map_smul]
  have hxq : X ((1 - P) v) = 0 := by
    by_contra hx
    have hq : (1 - P) v ≠ 0 := fun hq => hx (by rw [hq, map_zero])
    have hpxq : P (X ((1 - P) v)) = X ((1 - P) v) := by
      have hh := DFunLike.congr_fun hQX v
      change X ((1 - P) v) - P (X ((1 - P) v)) = 0 at hh
      exact (sub_eq_zero.mp hh).symm
    have hpq : P ((1 - P) v) = 0 := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, hPP,
        sub_self]
    exact hgap a (X ((1 - P) v)) ((1 - P) v) hx hq hpxq hpq hxqv hqv
  calc
    X v = X (P v) + X ((1 - P) v) := by
      rw [← map_add]
      congr 1
      simp
    _ = 0 := by rw [hxp, hxq, zero_add]

variable [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- With disjoint sector spectra, a commuting off-diagonal operator vanishes. -/
theorem offDiagonal_commuting_eq_zero {H P X : E →L[ℂ] E}
    (hH : star H = H) (hP : P * P = P) (hHP : H * P = P * H)
    (hHX : H * X = X * H) (hPX : P * X * P = 0)
    (hQX : (1 - P) * X * (1 - P) = 0) (hgap : HasDisjointSectorEigenvalues H P) : X = 0 := by
  have hsym : H.toLinearMap.IsSymmetric := (show IsSelfAdjoint H from hH).isSymmetric
  apply ContinuousLinearMap.coe_injective
  apply (hsym.eigenvectorBasis rfl).toBasis.ext
  intro i
  exact offDiagonal_commuting_kills_eigenvector hP hHP hHX hPX hQX hgap
    (hsym.apply_eigenvectorBasis rfl i)

/-- The gap superoperator is injective when the two spectral sectors are disjoint. -/
theorem gapSuperoperator_injective {H P : E →L[ℂ] E}
    (hH : star H = H) (hP : P * P = P) (hHP : H * P = P * H)
    (hgap : HasDisjointSectorEigenvalues H P) : Function.Injective (gapSuperoperator H P) := by
  apply (gapSuperoperator H P).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro X hX
  obtain ⟨hPX, hQX, hHX⟩ := gapSuperoperator_kernel hP hHP hX
  exact offDiagonal_commuting_eq_zero hH hP hHP hHX hPX hQX hgap

/-- A finite-dimensional spectral separation makes the fixed-space superoperator invertible. -/
theorem gapSuperoperator_isUnit {H P : E →L[ℂ] E}
    (hH : star H = H) (hP : P * P = P) (hHP : H * P = P * H)
    (hgap : HasDisjointSectorEigenvalues H P) : IsUnit (gapSuperoperator H P) := by
  have hinj := gapSuperoperator_injective hH hP hHP hgap
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

omit [FiniteDimensional ℂ E] in
/-- A positive numerical gap implies disjoint sector eigenvalues. -/
theorem hasDisjointSectorEigenvalues_of_gap {H P : E →L[ℂ] E} {g : ℝ}
    (hg : 0 < g)
    (hgap : ∀ (a b : ℝ) (v w : E), v ≠ 0 → w ≠ 0 → P v = v → P w = 0 →
      H v = (a : ℂ) • v → H w = (b : ℂ) • w → g ≤ |a - b|) :
    HasDisjointSectorEigenvalues H P := by
  intro a v w hv hw hPv hPw hHv hHw
  have hle := hgap a a v w hv hw hPv hPw hHv hHw
  have : g ≤ 0 := by simpa only [sub_self, abs_zero] using hle
  exact (not_le_of_gt hg) this

end SpectralSeparation

end Adiabatic
