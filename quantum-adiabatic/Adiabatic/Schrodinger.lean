import Adiabatic.Statement
import Adiabatic.Propagator
import Adiabatic.Transport
import Mathlib.Tactic

/-!
# Existence, unitarity, and uniqueness of physical evolution

Continuous Hamiltonians generate propagators on the unit interval.
Self-adjoint Hamiltonians give unitary evolution, and two solutions with the
same normalized initial value agree throughout that interval. Values outside
the interval are unconstrained, so uniqueness is stated as equality on it.
-/

noncomputable section

namespace Adiabatic

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Continuity of the Hamiltonian suffices to construct its normalized
Schrödinger evolution on the entire unit interval. -/
theorem exists_schrodingerEvolution {H : ℝ → Operator E}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1)) (T : ℝ) :
    ∃ U : ℝ → Operator E, IsSchrodingerEvolution E H T U := by
  obtain ⟨U, hU0, hU⟩ := exists_propagator_unitInterval
    (continuousOn_const.smul hH :
      ContinuousOn (fun t => (-Complex.I * (T : ℂ)) • H t) (Icc (0 : ℝ) 1))
  refine ⟨U, hU0, ?_⟩
  intro t ht
  simpa only [smul_mul_assoc] using hU t ht

/-- The physical generator is skew-adjoint for every real runtime. -/
theorem schrodinger_generator_skewAdjoint {H : Operator E} (hH : star H = H) (T : ℝ) :
    star ((-Complex.I * (T : ℂ)) • H) = -((-Complex.I * (T : ℂ)) • H) := by
  have hz : star (-Complex.I * (T : ℂ)) = -(-Complex.I * (T : ℂ)) := by simp
  simp only [star_smul, hz, hH, neg_smul]

/-- Every normalized Schrödinger solution for a self-adjoint Hamiltonian is
unitary on the interval, including when the Hilbert space is zero-dimensional. -/
theorem schrodingerEvolution_unitary {H : ℝ → Operator E} {T : ℝ}
    {U : ℝ → Operator E}
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (hU : IsSchrodingerEvolution E H T U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    U t ∈ unitary (Operator E) := by
  apply transport_mem_unitary_of_finiteDimensional (B := fun s => (-Complex.I * (T : ℂ)) • H s)
    ?_ (fun s hs => schrodinger_generator_skewAdjoint (hH s hs) T) hU.1 ht
  intro s hs
  simpa only [smul_mul_assoc] using hU.2 s hs

/-- Two physical propagators for the same self-adjoint Hamiltonian and runtime
coincide throughout the unit interval. -/
theorem schrodingerEvolution_unique {H : ℝ → Operator E} {T : ℝ}
    {U V : ℝ → Operator E}
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (hU : IsSchrodingerEvolution E H T U)
    (hV : IsSchrodingerEvolution E H T V) :
    EqOn U V (Icc (0 : ℝ) 1) := by
  let B : ℝ → Operator E := fun t => (-Complex.I * (T : ℂ)) • H t
  have hUd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt U (B t * U t) (Icc (0 : ℝ) 1) t := by
    simpa only [B, smul_mul_assoc] using hU.2 t ht
  have hVd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt V (B t * V t) (Icc (0 : ℝ) 1) t := by
    simpa only [B, smul_mul_assoc] using hV.2 t ht
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => star (V s) * U s) 0 (Icc (0 : ℝ) 1) t := by
    have hB : star (B t) = -B t := schrodinger_generator_skewAdjoint (hH t ht) T
    convert (hVd t ht).star.mul (hUd t ht) using 1
    simp only [star_mul, hB, mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  intro t ht
  have hc := constant_of_derivWithin_zero
    (fun s hs => (hzero s hs).differentiableWithinAt)
    (fun s hs => (hzero s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc_zero_one s ⟨hs.1, hs.2.le⟩)) t ht
  have hprod : star (V t) * U t = 1 := by
    simpa only [hU.1, hV.1, star_one, one_mul] using hc
  have hunit := schrodingerEvolution_unitary hH hV ht
  calc
    U t = (V t * star (V t)) * U t := by
      rw [Unitary.mul_star_self_of_mem hunit, one_mul]
    _ = V t * (star (V t) * U t) := mul_assoc _ _ _
    _ = V t := by rw [hprod, mul_one]

/-- The gapped Hamiltonian has a unique unitary physical evolution on
the unit interval for every runtime. -/
theorem GappedHamiltonian.exists_unique_unitary_evolution (data : GappedHamiltonian E) (T : ℝ) :
    ∃ U : ℝ → Operator E,
      IsSchrodingerEvolution E data.H T U ∧
      (∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary (Operator E)) ∧
      ∀ V : ℝ → Operator E,
        IsSchrodingerEvolution E data.H T V → EqOn V U (Icc (0 : ℝ) 1) := by
  obtain ⟨U, hU⟩ := exists_schrodingerEvolution data.hamiltonian_smooth.continuous.continuousOn T
  have hH : ∀ t ∈ Icc (0 : ℝ) 1, star (data.H t) = data.H t :=
    fun t _ => data.hamiltonian_selfAdjoint t
  refine ⟨U, hU, fun _ ht => schrodingerEvolution_unitary hH hU ht, ?_⟩
  intro V hV
  exact schrodingerEvolution_unique hH hV hU

end Adiabatic
