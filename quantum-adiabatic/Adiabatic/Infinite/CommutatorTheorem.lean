import Adiabatic.Comparison
import Adiabatic.Leakage
import Adiabatic.Infinite.Unitary

/-!
# Bounded adiabatic commutator theorem in arbitrary dimension

The bounded physical and comparison generators produce unitary
propagators, including on infinite-dimensional Hilbert spaces. A continuously
differentiable solution `X` of `[H,X] = [P',P]` gives uniform `C / T` leakage.
All coefficient paths are fixed before the runtime is chosen.

The Hamiltonians are bounded and the commutator solution is supplied.
`Adiabatic.Infinite.SpectralTheorem` constructs that solution from a spectral gap.
-/

namespace Adiabatic.Infinite

open Set

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [StarRing A] [CStarRing A] [StarModule ℂ A]
  [CompleteSpace A] [Nontrivial A]

/-- The inverse of the Schrödinger scaling parameter has norm `1 / T`. -/
theorem norm_inv_schrodinger_parameter {T : ℝ} (hT : 0 < T) :
    ‖(-Complex.I * (T : ℂ))⁻¹‖ = 1 / T := by
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, one_div]

/-- A C¹ commutator solution gives a uniform adiabatic leakage bound. -/
theorem exists_adiabatic_bound_of_commutator
    (H P dP X dX : ℝ → A)
    (hHcont : ContinuousOn H (Icc (0 : ℝ) 1))
    (hdPcont : ContinuousOn dP (Icc (0 : ℝ) 1))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) 1))
    (hdXcont : ContinuousOn dX (Icc (0 : ℝ) 1))
    (hHstar : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (hPstar : ∀ t ∈ Icc (0 : ℝ) 1, star (P t) = P t)
    (hPid : ∀ t ∈ Icc (0 : ℝ) 1, P t * P t = P t)
    (hHP : ∀ t ∈ Icc (0 : ℝ) 1, H t * P t = P t * H t)
    (hPderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt P (dP t) (Icc 0 1) t)
    (hXderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1,
      H t * X t - X t * H t = katoGenerator (P t) (dP t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ U : ℝ → A,
      U 0 = 1 →
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - P t) * U t * P 0‖ ≤ C / T := by
  let K : ℝ → A := fun t => katoGenerator (P t) (dP t)
  have hPcont : ContinuousOn P (Icc (0 : ℝ) 1) :=
    fun t ht => (hPderiv t ht).continuousWithinAt
  have hKcont : ContinuousOn K (Icc (0 : ℝ) 1) :=
    (hdPcont.mul hPcont).sub (hPcont.mul hdPcont)
  have hKstar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : star (K t) = -K t :=
    star_katoGenerator_of_hasDerivWithinAt hPstar ht
      (uniqueDiffOn_Icc_zero_one t ht) (hPderiv t ht)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hXcont
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hdXcont
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hKcont
  have hMnonneg : 0 ≤ M := (norm_nonneg (X 0)).trans (hM 0 (by simp))
  have hDnonneg : 0 ≤ D := (norm_nonneg (dX 0)).trans (hD 0 (by simp))
  have hLnonneg : 0 ≤ L := (norm_nonneg (K 0)).trans (hL 0 (by simp))
  refine ⟨2 * M + D + L * M, by positivity, ?_⟩
  intro T hT U hU0 hU t ht
  let z : ℂ := -Complex.I * (T : ℂ)
  have hz : z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hT.ne')
  have hzstar : star z = -z := by simp [z]
  have hGstar (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      star (z • H u) = -(z • H u) := by
    simp only [star_smul, hzstar, hHstar u hu, neg_smul]
  obtain ⟨V, hV0, hV⟩ := exists_propagator_unitInterval
    ((continuousOn_const.smul hHcont).add hKcont :
      ContinuousOn (fun u => z • H u + K u) (Icc (0 : ℝ) 1))
  have hVstar (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      star (z • H u + K u) = -(z • H u + K u) := by
    rw [star_add, hGstar u hu, hKstar u hu, neg_add]
  have hU' (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt U ((z • H u) * U u) (Icc 0 1) u := by
    simpa only [smul_mul_assoc] using hU u hu
  have hUunitary (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : U u ∈ unitary A :=
    transport_mem_unitary (continuousOn_const.smul hHcont) hU' hGstar hU0 hu
  have hVunitary (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : V u ∈ unitary A :=
    transport_mem_unitary ((continuousOn_const.smul hHcont).add hKcont) hV hVstar hV0 hu
  have hinter : P t * V t = V t * P 0 := by
    apply kato_transport_intertwines hPid hPstar hPderiv hV hGstar ?_ hV0 ht
      (hVunitary t ht)
    intro u hu
    simp only [smul_mul_assoc, mul_smul_comm, hHP u hu]
  have hcomparison := adiabatic_comparison H K X dX U V z M D L hz hzstar
    hHstar hKstar hU
    (fun u hu => by simpa only [Pi.add_apply, add_mul, smul_mul_assoc] using hV u hu)
    hXderiv hcomm hUunitary hVunitary hU0 hV0 hM hD hL ht
  calc
    ‖(1 - P t) * U t * P 0‖ ≤ ‖U t - V t‖ :=
      leakage_le_comparison _ _ _ _ (hPid t ht) (hPstar t ht)
        (hPid 0 (by simp)) (hPstar 0 (by simp)) hinter
    _ ≤ ‖z⁻¹‖ * (2 * M + t * (D + L * M)) := hcomparison
    _ ≤ (1 / T) * (2 * M + (D + L * M)) := by
      rw [norm_inv_schrodinger_parameter hT]
      gcongr
      exact mul_le_of_le_one_left (by positivity) ht.2
    _ = (2 * M + D + L * M) / T := by ring

omit [Nontrivial A] in
/-- A continuous bounded self-adjoint Hamiltonian has a normalized
unitary Schrödinger propagator for every runtime, in arbitrary
dimension. The derivative is in operator norm. -/
theorem exists_unitary_schrodinger_propagator
    (H : ℝ → A)
    (hHcont : ContinuousOn H (Icc (0 : ℝ) 1))
    (hHstar : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (T : ℝ) :
    ∃ U : ℝ → A, U 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary A := by
  let z : ℂ := -Complex.I * (T : ℂ)
  have hzstar : star z = -z := by simp [z]
  have hGstar (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      star (z • H u) = -(z • H u) := by
    simp only [star_smul, hzstar, hHstar u hu, neg_smul]
  obtain ⟨U, hU0, hU, hUunitary⟩ :=
    exists_unitary_propagator_unitInterval (continuousOn_const.smul hHcont) hGstar
  exact ⟨U, hU0, fun t ht => by simpa only [smul_mul_assoc] using hU t ht, hUunitary⟩

/-- For bounded Hamiltonians in arbitrary dimension, a C¹ commutator
solution gives both unitary Schrödinger evolution and a uniform adiabatic
leakage estimate. -/
theorem exists_unitary_adiabatic_evolution_of_commutator
    (H P dP X dX : ℝ → A)
    (hHcont : ContinuousOn H (Icc (0 : ℝ) 1))
    (hdPcont : ContinuousOn dP (Icc (0 : ℝ) 1))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) 1))
    (hdXcont : ContinuousOn dX (Icc (0 : ℝ) 1))
    (hHstar : ∀ t ∈ Icc (0 : ℝ) 1, star (H t) = H t)
    (hPstar : ∀ t ∈ Icc (0 : ℝ) 1, star (P t) = P t)
    (hPid : ∀ t ∈ Icc (0 : ℝ) 1, P t * P t = P t)
    (hHP : ∀ t ∈ Icc (0 : ℝ) 1, H t * P t = P t * H t)
    (hPderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt P (dP t) (Icc 0 1) t)
    (hXderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt X (dX t) (Icc 0 1) t)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1,
      H t * X t - X t * H t = katoGenerator (P t) (dP t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∃ U : ℝ → A,
      U 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary A) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 - P t) * U t * P 0‖ ≤ C / T := by
  obtain ⟨C, hC, hbound⟩ := exists_adiabatic_bound_of_commutator H P dP X dX
    hHcont hdPcont hXcont hdXcont hHstar hPstar hPid hHP hPderiv hXderiv hcomm
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨U, hU0, hU, hUunitary⟩ := exists_unitary_schrodinger_propagator H hHcont hHstar T
  exact ⟨U, hU0, hU, hUunitary, hbound T hT U hU0 hU⟩

end Adiabatic.Infinite
