import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Statement of the finite-dimensional adiabatic theorem

The hypotheses and conclusion of `Adiabatic.MainTheorem` are defined here.
Operators carry the Hilbert-space operator norm and time derivatives are real.
-/

noncomputable section

namespace Adiabatic

open Set

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Operators on the finite-dimensional complex Hilbert space. -/
abbrev Operator := E →L[ℂ] E

/-- A gap between the selected spectral subspace and its complement.
The eigenvalue formulation avoids choosing eigenvectors smoothly in time.
In finite dimension self-adjoint operators have orthonormal eigenbases. -/
def HasUniformSpectralGap (H P : ℝ → Operator E) (g : ℝ) : Prop :=
  0 < g ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ (a b : ℝ) (v w : E),
    v ≠ 0 → w ≠ 0 → P t v = v → P t w = 0 →
    H t v = (a : ℂ) • v → H t w = (b : ℂ) • w → g ≤ |a - b|

/-- Smooth self-adjoint Hamiltonian and selected orthogonal spectral projection.
The paths are defined smoothly on all real times to avoid endpoint conventions;
the gap is required only on the closed unit interval. -/
structure GappedHamiltonian where
  H : ℝ → Operator E
  P : ℝ → Operator E
  hamiltonian_smooth : ContDiff ℝ 2 H
  projection_smooth : ContDiff ℝ 2 P
  hamiltonian_selfAdjoint : ∀ t, star (H t) = H t
  projection_selfAdjoint : ∀ t, star (P t) = P t
  projection_idempotent : ∀ t, P t * P t = P t
  commutes : ∀ t, H t * P t = P t * H t
  gap : ℝ
  spectral_gap : HasUniformSpectralGap E H P gap

/-- Physical Schrödinger evolution, with scaled time and `ℏ = 1`. -/
def IsSchrodingerEvolution (H : ℝ → Operator E) (T : ℝ)
    (U : ℝ → Operator E) : Prop :=
  U 0 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t

/-- Existence of the physical propagator for every positive runtime. -/
def HasSchrodingerEvolution (H : ℝ → Operator E) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ U : ℝ → Operator E, IsSchrodingerEvolution E H T U

/-- The leakage estimate. The constant is chosen before the runtime
and the solution, so the quantifiers require a uniform adiabatic limit. -/
def HasUniformAdiabaticEstimate (H P : ℝ → Operator E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ U : ℝ → Operator E,
    IsSchrodingerEvolution E H T U → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(1 - P t) * U t * P 0‖ ≤ C / T

/-- Existence of Schrödinger evolution and a uniform adiabatic leakage bound.
Proved in `Adiabatic.MainTheorem`. -/
def FiniteDimensionalAdiabaticTheorem : Prop :=
  ∀ data : GappedHamiltonian E,
    HasSchrodingerEvolution E data.H ∧ HasUniformAdiabaticEstimate E data.H data.P

end Adiabatic
