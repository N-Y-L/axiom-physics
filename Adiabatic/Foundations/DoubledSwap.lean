import Adiabatic.Foundations.StrongSwapInverse
import Adiabatic.Unbounded.Statement
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The explicit doubled swap common-domain Hamiltonian

A bounded bijection into a Hilbert space gives a common domain in the Hilbert
direct sum. Its constant swap Hamiltonian is constructed here before the exact
adiabatic theorem is applied. The bounded inverse is extracted from the domain
lift of the resulting quarter-turn propagator.
-/

noncomputable section

namespace Adiabatic.Foundations

open Set Adiabatic.Unbounded

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hilbert direct sum, with its Euclidean product norm. -/
abbrev SwapSpace (E : Type*) := WithLp 2 (E × E)

/-- The first physical coordinate. -/
def swapFirst : SwapSpace E →L[ℂ] E := WithLp.fstL 2 ℂ E E

/-- The second physical coordinate. -/
def swapSecond : SwapSpace E →L[ℂ] E := WithLp.sndL 2 ℂ E E

/-- Inclusion of the doubled domain into the physical Hilbert direct sum. -/
def doubledInclusion (j : D →L[ℂ] E) : (D × E) →L[ℂ] SwapSpace E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    ((j.comp (ContinuousLinearMap.fst ℂ D E)).prod (ContinuousLinearMap.snd ℂ D E))

@[simp] theorem doubledInclusion_apply (j : D →L[ℂ] E) (d : D × E) :
    doubledInclusion j d = WithLp.toLp 2 (j d.1, d.2) := rfl

/-- The bounded physical operator exchanging the two Hilbert coordinates. -/
def physicalSwap : SwapSpace E →L[ℂ] SwapSpace E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    ((swapSecond (E := E)).prod swapFirst)

@[simp] theorem physicalSwap_apply (x : SwapSpace E) :
    physicalSwap x = WithLp.toLp 2 (x.snd, x.fst) := rfl

@[simp] theorem physicalSwap_involutive (x : SwapSpace E) :
    physicalSwap (physicalSwap x) = x := by
  change WithLp.toLp 2 (WithLp.ofLp x) = x
  exact WithLp.toLp_ofLp _ _

theorem doubledInclusion_bijective (j : D →L[ℂ] E) (hj : Function.Bijective j) :
    Function.Bijective (doubledInclusion j) := by
  constructor
  · intro x y h
    have ha := congrArg (swapFirst (E := E)) h
    have hb := congrArg (swapSecond (E := E)) h
    exact Prod.ext (hj.1 ha) hb
  · intro y
    obtain ⟨x, hx⟩ := hj.2 y.fst
    refine ⟨(x, y.snd), ?_⟩
    simp only [doubledInclusion_apply, hx]
    change WithLp.toLp 2 (WithLp.ofLp y) = y
    exact WithLp.toLp_ofLp _ _

/-- The constructed common domain uses only the algebraic bijectivity of `j`. -/
def doubledDomain (j : D →L[ℂ] E) (hj : Function.Bijective j) :
    CommonDomain (D × E) (SwapSpace E) where
  inclusion := doubledInclusion j
  injective := (doubledInclusion_bijective j hj).1
  dense := (doubledInclusion_bijective j hj).2.denseRange

/-- The Hamiltonian on domain coordinates, `(x,y) ↦ (y,j x)`. -/
def doubledHamiltonian (j : D →L[ℂ] E) : (D × E) →L[ℂ] SwapSpace E :=
  physicalSwap.comp (doubledInclusion j)

@[simp] theorem doubledHamiltonian_apply (j : D →L[ℂ] E) (d : D × E) :
    doubledHamiltonian j d = WithLp.toLp 2 (d.2, j d.1) := rfl

variable [CompleteSpace E]

/-- The physical swap is self-adjoint for the Hilbert sum inner product. -/
theorem physicalSwap_selfAdjoint : _root_.IsSelfAdjoint (physicalSwap (E := E)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp [WithLp.prod_inner_apply, add_comm]

omit [CompleteSpace E] in
/-- The common-domain partial operator is precisely the everywhere defined swap. -/
theorem doubledDomain_operator (j : D →L[ℂ] E) (hj : Function.Bijective j) :
    (doubledDomain j hj).operator (doubledHamiltonian j) =
      (physicalSwap (E := E)).toPMap ⊤ := by
  apply LinearPMap.ext
  · exact LinearMap.range_eq_top.mpr (doubledInclusion_bijective j hj).2
  · intro x hx _
    change physicalSwap ((doubledDomain j hj).inclusion
      ((doubledDomain j hj).rangeEquiv.symm ⟨x, hx⟩)) = physicalSwap x
    rw [CommonDomain.inclusion_rangeEquiv_symm]

/-- Self-adjointness is checked for the original partial-operator definition. -/
theorem doubledHamiltonian_selfAdjoint (j : D →L[ℂ] E) (hj : Function.Bijective j) :
    (doubledDomain j hj).IsSelfAdjoint (doubledHamiltonian j) := by
  change _root_.IsSelfAdjoint ((doubledDomain j hj).operator (doubledHamiltonian j))
  rw [doubledDomain_operator, LinearPMap.isSelfAdjoint_def,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ (by simp)]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp physicalSwap_selfAdjoint]

omit [CompleteSpace E] in
/-- The algebraic factorization of the physical swap pencil. -/
theorem physicalSwap_pencil_identity (z : ℂ) (x : SwapSpace E) :
    physicalSwap (physicalSwap x - z • x) + z • (physicalSwap x - z • x) =
      (1 - z * z) • x := by
  simp only [map_sub, map_smul, physicalSwap_involutive]
  module

omit [CompleteSpace E] in
/-- Away from the two eigenvalues the physical pencil is algebraically bijective. -/
theorem physicalSwap_pencil_bijective (z : ℂ) (hz : 1 - z * z ≠ 0) :
    Function.Bijective (fun x : SwapSpace E => physicalSwap x - z • x) := by
  constructor
  · intro x y h
    have h' := congrArg (fun v : SwapSpace E => physicalSwap v + z • v) h
    dsimp only at h'
    rw [physicalSwap_pencil_identity, physicalSwap_pencil_identity] at h'
    have h'' := congrArg (fun v : SwapSpace E => (1 - z * z)⁻¹ • v) h'
    simpa [smul_smul, hz] using h''
  · intro y
    refine ⟨(1 - z * z)⁻¹ • (physicalSwap y + z • y), ?_⟩
    have h : physicalSwap (physicalSwap y + z • y) -
        z • (physicalSwap y + z • y) = (1 - z * z) • y := by
      simp only [map_add, map_smul, physicalSwap_involutive]
      module
    calc
      physicalSwap ((1 - z * z)⁻¹ • (physicalSwap y + z • y)) -
          z • ((1 - z * z)⁻¹ • (physicalSwap y + z • y)) =
          (1 - z * z)⁻¹ • (physicalSwap (physicalSwap y + z • y) -
            z • (physicalSwap y + z • y)) := by
              simp only [map_smul, smul_sub, smul_smul]
              module
      _ = y := by rw [h]; simp [smul_smul, hz]

omit [CompleteSpace E] in
/-- The original common-domain algebraic spectrum is contained in the swap values. -/
theorem doubledHamiltonian_spectrum_subset (j : D →L[ℂ] E)
    (hj : Function.Bijective j) {z : ℂ}
    (hz : z ∈ (doubledDomain j hj).spectrum (doubledHamiltonian j)) :
    z = 1 ∨ z = -1 := by
  by_contra h
  have hc : 1 - z * z ≠ 0 := by
    intro hc
    have hp : (z - 1) * (z + 1) = 0 := by linear_combination -hc
    rcases mul_eq_zero.mp hp with hp | hp
    · exact h (Or.inl (sub_eq_zero.mp hp))
    · exact h (Or.inr (eq_neg_of_add_eq_zero_left hp))
  exact hz ((physicalSwap_pencil_bijective z hc).comp (doubledInclusion_bijective j hj))

omit [CompleteSpace E] in
/-- On a nonzero Hilbert space both swap values occur in the exact algebraic spectrum. -/
theorem doubledHamiltonian_spectrum_eq [Nontrivial E] (j : D →L[ℂ] E)
    (hj : Function.Bijective j) :
    (doubledDomain j hj).spectrum (doubledHamiltonian j) = {1, -1} := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨x, hx⟩ := hj.2 v
  have hp : (1 : ℂ) ∈ (doubledDomain j hj).spectrum (doubledHamiltonian j) := by
    intro hb
    have heq : (x, v) = (0 : D × E) := hb.1 (show
        (doubledDomain j hj).shift (doubledHamiltonian j) 1 (x, v) =
          (doubledDomain j hj).shift (doubledHamiltonian j) 1 0 from by
      rw [map_zero, CommonDomain.shift_apply]
      change WithLp.toLp 2 (v, j x) - (1 : ℂ) • WithLp.toLp 2 (j x, v) = 0
      simp [hx])
    exact hv (congrArg Prod.snd heq)
  have hm : (-1 : ℂ) ∈ (doubledDomain j hj).spectrum (doubledHamiltonian j) := by
    intro hb
    have heq : (x, -v) = (0 : D × E) := hb.1 (show
        (doubledDomain j hj).shift (doubledHamiltonian j) (-1) (x, -v) =
          (doubledDomain j hj).shift (doubledHamiltonian j) (-1) 0 from by
      rw [map_zero, CommonDomain.shift_apply]
      change WithLp.toLp 2 (-v, j x) - (-1 : ℂ) • WithLp.toLp 2 (j x, -v) = 0
      rw [hx, neg_one_smul, sub_neg_eq_add]
      apply WithLp.ofLp_injective 2
      change (-v, v) + (v, -v) = (0, 0)
      simp)
    exact hv (neg_eq_zero.mp (congrArg Prod.snd heq))
  ext z
  constructor
  · intro hz
    rcases doubledHamiltonian_spectrum_subset j hj hz with rfl | rfl <;> simp
  · intro hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hp
    · simpa only [Set.mem_singleton_iff] using hz ▸ hm

/-- The explicit constant swap satisfies all the original gapped-Hamiltonian hypotheses. -/
def doubledGappedHamiltonian (j : D →L[ℂ] E) (hj : Function.Bijective j) :
    GappedHamiltonian (doubledDomain j hj) where
  H := fun _ => doubledHamiltonian j
  smooth := contDiffOn_const
  selfAdjoint := fun _ _ => doubledHamiltonian_selfAdjoint j hj
  lower := fun _ => 0
  upper := fun _ => 2
  lower_continuous := continuousOn_const
  upper_continuous := continuousOn_const
  band_ordered := by intros; norm_num
  gap := 1
  gap_positive := by norm_num
  spectral_gap := by
    intro t ht w hw
    rcases doubledHamiltonian_spectrum_subset j hj hw with rfl | rfl <;>
      norm_num [Complex.norm_def]

/-- Applying the exact theorem to the constructed swap yields the inverse from its lift. -/
theorem bounded_inverse_of_doubled_adiabatic_theorem (j : D →L[ℂ] E)
    (hj : Function.Bijective j)
    (hQAT : CommonDomainAdiabaticTheorem (doubledDomain j hj)) :
    ∃ R : E →L[ℂ] D, (∀ y, j (R y) = y) ∧ (∀ x, R (j x) = x) := by
  obtain ⟨U⟩ := (hQAT (doubledGappedHamiltonian j hj)).2.2.1
    (Real.pi / 2) (by positivity)
  exact bounded_inverse_of_strong_swap j hj.1 (doubledDomain j hj)
    (doubledHamiltonian j) U swapFirst swapSecond
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end Adiabatic.Foundations
