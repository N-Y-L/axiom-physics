import Adiabatic.Evolution
import Adiabatic.Projection
import Adiabatic.SpectralGap
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Regularity and bounds for inverse commutator constructions

Smooth inversion is used only where invertibility has been established.
Compactness supplies uniform constants for a continuously
differentiable path and its derivative.
-/

namespace Adiabatic

section Inverse

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- A smooth path of invertible elements has a smooth inverse path. -/
theorem contDiffOn_ringInverse {n : WithTop ℕ∞} {L : ℝ → B} {s : Set ℝ}
    (hL : ContDiffOn ℝ n L s) (hunit : ∀ t ∈ s, IsUnit (L t)) :
    ContDiffOn ℝ n (fun t => Ring.inverse (L t)) s := by
  intro t ht
  obtain ⟨u, hu⟩ := hunit t ht
  have hi := contDiffAt_ringInverse (n := n) ℝ u
  rw [hu] at hi
  exact hi.comp_contDiffWithinAt t (hL t ht)

end Inverse

section Apply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Complex operator application is smooth also for real-time paths. -/
theorem contDiffOn_complex_apply {n : WithTop ℕ∞}
    {L : ℝ → E →L[ℂ] E} {K : ℝ → E} {s : Set ℝ}
    (hL : ContDiffOn ℝ n L s) (hK : ContDiffOn ℝ n K s) :
    ContDiffOn ℝ n (fun t => L t (K t)) s := by
  exact ((isBoundedBilinearMap_apply (𝕜 := ℂ) (E := E) (F := E)).contDiff.restrict_scalars ℝ).comp₂_contDiffOn hL hK

variable [CompleteSpace E]

/-- Solving a smooth family of invertible linear equations preserves regularity. -/
theorem contDiffOn_inverse_apply {n : WithTop ℕ∞}
    {L : ℝ → E →L[ℂ] E} {K : ℝ → E} {s : Set ℝ}
    (hL : ContDiffOn ℝ n L s) (hK : ContDiffOn ℝ n K s)
    (hunit : ∀ t ∈ s, IsUnit (L t)) :
    ContDiffOn ℝ n (fun t => Ring.inverse (L t) (K t)) s :=
  contDiffOn_complex_apply (contDiffOn_ringInverse hL hunit) hK

end Apply

section Superoperator

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Multiplication on the left and right depends smoothly on both factors. -/
theorem contDiffOn_mulLeftRight {n : WithTop ℕ∞} {P Q : ℝ → A} {s : Set ℝ}
    (hP : ContDiffOn ℝ n P s) (hQ : ContDiffOn ℝ n Q s) :
    ContDiffOn ℝ n (fun t => ContinuousLinearMap.mulLeftRight ℂ A (P t) (Q t)) s := by
  exact ((ContinuousLinearMap.mulLeftRight_isBoundedBilinear ℂ A).contDiff.restrict_scalars ℝ).comp₂_contDiffOn hP hQ

/-- The diagonal block superoperator is smooth in a smooth projection path. -/
theorem contDiffOn_diagonalSuperoperator {n : WithTop ℕ∞} {P : ℝ → A} {s : Set ℝ}
    (hP : ContDiffOn ℝ n P s) :
    ContDiffOn ℝ n (fun t => diagonalSuperoperator (P t)) s := by
  have hQ : ContDiffOn ℝ n (fun t => 1 - P t) s := contDiffOn_const.sub hP
  exact (contDiffOn_mulLeftRight hP hP).add (contDiffOn_mulLeftRight hQ hQ)

/-- The off-diagonal block superoperator is smooth in a smooth projection path. -/
theorem contDiffOn_offDiagonalSuperoperator {n : WithTop ℕ∞} {P : ℝ → A} {s : Set ℝ}
    (hP : ContDiffOn ℝ n P s) :
    ContDiffOn ℝ n (fun t => offDiagonalSuperoperator (P t)) s := by
  have hQ : ContDiffOn ℝ n (fun t => 1 - P t) s := contDiffOn_const.sub hP
  exact (contDiffOn_mulLeftRight hP hQ).add (contDiffOn_mulLeftRight hQ hP)

/-- The fixed-space gap superoperator varies smoothly with `H` and `P`. -/
theorem contDiffOn_gapSuperoperator {n : WithTop ℕ∞} {H P : ℝ → A} {s : Set ℝ}
    (hH : ContDiffOn ℝ n H s) (hP : ContDiffOn ℝ n P s) :
    ContDiffOn ℝ n (fun t => gapSuperoperator (H t) (P t)) s := by
  have hleft : ContDiffOn ℝ n (fun t => ContinuousLinearMap.mul ℂ A (H t)) s :=
    ((ContinuousLinearMap.mul ℂ A).contDiff.restrict_scalars ℝ).comp_contDiffOn hH
  have hright : ContDiffOn ℝ n (fun t => (ContinuousLinearMap.mul ℂ A).flip (H t)) s :=
    ((ContinuousLinearMap.mul ℂ A).flip.contDiff.restrict_scalars ℝ).comp_contDiffOn hH
  have hcomp := ((isBoundedBilinearMap_comp (𝕜 := ℂ) (E := A) (F := A)
    (G := A)).contDiff.restrict_scalars ℝ).comp₂_contDiffOn
      (hleft.sub hright) (contDiffOn_offDiagonalSuperoperator hP)
  exact (contDiffOn_diagonalSuperoperator hP).add hcomp

/-- A `C²` projection path has a `C¹` Kato generator using its derivative. -/
theorem contDiffOn_katoGenerator_derivWithin {P : ℝ → A} {s : Set ℝ}
    (hP : ContDiffOn ℝ 2 P s) (hs : UniqueDiffOn ℝ s) :
    ContDiffOn ℝ 1 (fun t => katoGenerator (P t) (derivWithin P s t)) s := by
  have hD : ContDiffOn ℝ 1 (derivWithin P s) s := hP.derivWithin hs (by norm_num)
  have hP1 : ContDiffOn ℝ 1 P s := hP.of_le (by norm_num)
  exact (hD.mul hP1).sub (hP1.mul hD)

variable [CompleteSpace A]

/-- The inverse gap superoperator produces a `C¹` candidate commutator path.
Its commutator equation follows separately from the inverse's algebraic properties. -/
theorem contDiffOn_gapInverse_katoGenerator {H P : ℝ → A} {s : Set ℝ}
    (hH : ContDiffOn ℝ 1 H s) (hP : ContDiffOn ℝ 2 P s)
    (hs : UniqueDiffOn ℝ s)
    (hunit : ∀ t ∈ s, IsUnit (gapSuperoperator (H t) (P t))) :
    ContDiffOn ℝ 1
      (fun t => Ring.inverse (gapSuperoperator (H t) (P t))
        (katoGenerator (P t) (derivWithin P s t))) s :=
  contDiffOn_inverse_apply (contDiffOn_gapSuperoperator hH (hP.of_le (by norm_num)))
    (contDiffOn_katoGenerator_derivWithin hP hs) hunit

/-- A C¹ invertible gap superoperator gives a C¹ commutator
solution, with the projection derivative taken within the stated domain. -/
theorem exists_contDiffOn_commutator_of_isUnit {H P : ℝ → A} {s : Set ℝ}
    (hH : ContDiffOn ℝ 1 H s) (hP : ContDiffOn ℝ 2 P s)
    (hs : UniqueDiffOn ℝ s)
    (hPP : ∀ t ∈ s, P t * P t = P t)
    (hHP : ∀ t ∈ s, H t * P t = P t * H t)
    (hunit : ∀ t ∈ s, IsUnit (gapSuperoperator (H t) (P t))) :
    ∃ X : ℝ → A, ContDiffOn ℝ 1 X s ∧ ∀ t ∈ s,
      H t * X t - X t * H t = katoGenerator (P t) (derivWithin P s t) := by
  refine ⟨fun t => commutatorSolution (H t) (P t)
    (katoGenerator (P t) (derivWithin P s t)), ?_, ?_⟩
  · exact contDiffOn_gapInverse_katoGenerator hH hP hs hunit
  · intro t ht
    exact commutatorSolution_katoGenerator (hPP t ht) (hHP t ht) (hunit t ht)
      (derivWithin P s t)

end Superoperator

section SpectralSolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Finite-dimensional spectral separation and smooth data produce a `C¹`
commutator solution; no smooth choice of eigenvectors is assumed. -/
theorem exists_contDiffOn_commutator_of_spectral_separation
    {H P : ℝ → E →L[ℂ] E} {s : Set ℝ}
    (hH : ContDiffOn ℝ 1 H s) (hP : ContDiffOn ℝ 2 P s)
    (hs : UniqueDiffOn ℝ s)
    (hHstar : ∀ t ∈ s, star (H t) = H t)
    (hPP : ∀ t ∈ s, P t * P t = P t)
    (hHP : ∀ t ∈ s, H t * P t = P t * H t)
    (hgap : ∀ t ∈ s, HasDisjointSectorEigenvalues (H t) (P t)) :
    ∃ X : ℝ → E →L[ℂ] E, ContDiffOn ℝ 1 X s ∧ ∀ t ∈ s,
      H t * X t - X t * H t = katoGenerator (P t) (derivWithin P s t) :=
  exists_contDiffOn_commutator_of_isUnit hH hP hs hPP hHP
    (fun t ht => gapSuperoperator_isUnit (hHstar t ht) (hPP t ht) (hHP t ht) (hgap t ht))

end SpectralSolution

section CompactBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On the unit interval, a `C¹` path and a continuous generator have finite
nonnegative bounds, including a bound on the within-interval derivative. -/
theorem exists_uniform_bounds {X K : ℝ → E}
    (hX : ContDiffOn ℝ 1 X (Set.Icc 0 1))
    (hK : ContinuousOn K (Set.Icc 0 1)) :
    ∃ MX MD MK : ℝ, 0 ≤ MX ∧ 0 ≤ MD ∧ 0 ≤ MK ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖X t‖ ≤ MX ∧ ‖derivWithin X (Set.Icc 0 1) t‖ ≤ MD ∧ ‖K t‖ ≤ MK := by
  have hs : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hD := hX.continuousOn_derivWithin hs (by rfl)
  obtain ⟨MX, hMX⟩ := isCompact_Icc.exists_bound_of_continuousOn hX.continuousOn
  obtain ⟨MD, hMD⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  obtain ⟨MK, hMK⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨MX, MD, MK, (norm_nonneg _).trans (hMX 0 h0),
    (norm_nonneg _).trans (hMD 0 h0), (norm_nonneg _).trans (hMK 0 h0), ?_⟩
  intro t ht
  exact ⟨hMX t ht, hMD t ht, hMK t ht⟩

end CompactBounds

end Adiabatic
