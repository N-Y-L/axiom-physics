import Adiabatic.Unbounded.Propagator
import Adiabatic.Foundations.SwapScalarEvolution

/-!
# The constant-swap obstruction for the actual strong propagator

Two bounded physical coordinate functionals that the Hamiltonian exchanges
obey the scalar swap equation. The supplied strong propagator therefore
transfers their initial values at a quarter turn. This derives the necessary
coordinate identity directly from `StrongPropagator.strong_derivative`;
it does not assume that a comparison evolution has a bounded domain lift.
-/

namespace Adiabatic.Foundations

open Set Adiabatic.Unbounded

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A strong propagator for a constant Hamiltonian exchanging two physical
coordinates has the forced quarter-turn values on an initially first-coordinate
vector. Completeness or self-adjointness of a hypothetical example is not
inferred by this lemma. -/
theorem strongPropagator_swap_coordinates (domain : CommonDomain D E)
    (H : D →L[ℂ] E)
    (U : StrongPropagator domain (fun _ => H) (fun _ => 0)
      (-Complex.I * (Real.pi / 2 : ℝ)))
    (a b : E →L[ℂ] ℂ)
    (ha : ∀ d : D, a (H d) = b (domain.inclusion d))
    (hb : ∀ d : D, b (H d) = a (domain.inclusion d))
    (x : D) (hax : a (domain.inclusion x) = 1)
    (hbx : b (domain.inclusion x) = 0) :
    a (domain.inclusion (U.lift 1 x)) = 0 ∧
      b (domain.inclusion (U.lift 1 x)) = -Complex.I := by
  let f : ℝ → ℂ := fun t => a (U.evolution t (domain.inclusion x))
  let g : ℝ → ℂ := fun t => b (U.evolution t (domain.inclusion x))
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt f ((-Complex.I * (Real.pi / 2 : ℝ)) * g t) (Icc 0 1) t := by
    have hd := (a.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (U.strong_derivative x t ht)
    simpa [f, g, ha, U.preserves_domain t ht] using hd
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g ((-Complex.I * (Real.pi / 2 : ℝ)) * f t) (Icc 0 1) t := by
    have hd := (b.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (U.strong_derivative x t ht)
    simpa [f, g, hb, U.preserves_domain t ht] using hd
  have hzeroF : f 0 = 1 := by simpa [f, U.initial] using hax
  have hzeroG : g 0 = 0 := by simpa [g, U.initial] using hbx
  have hv := swap_quarter_turn_coordinates f g hf hg hzeroF hzeroG
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  simpa [f, g, U.preserves_domain 1 ht] using hv

/-- A weighted output coordinate bounds the norm of the actual domain lift
from below. The only trajectory used is the given strong propagator. -/
theorem strongPropagator_swap_lift_norm_lower (domain : CommonDomain D E)
    (H : D →L[ℂ] E)
    (U : StrongPropagator domain (fun _ => H) (fun _ => 0)
      (-Complex.I * (Real.pi / 2 : ℝ)))
    (a b : E →L[ℂ] ℂ)
    (ha : ∀ d : D, a (H d) = b (domain.inclusion d))
    (hb : ∀ d : D, b (H d) = a (domain.inclusion d))
    (x : D) (hax : a (domain.inclusion x) = 1)
    (hbx : b (domain.inclusion x) = 0) (hx : ‖x‖ ≤ 1)
    (w : ℝ) (hw : ∀ d : D, w * ‖b (domain.inclusion d)‖ ≤ ‖d‖) :
    w ≤ ‖U.lift 1‖ := by
  have hvalue := (strongPropagator_swap_coordinates domain H U a b ha hb x hax hbx).2
  have hlower : w ≤ ‖U.lift 1 x‖ := by simpa [hvalue] using hw (U.lift 1 x)
  exact hlower.trans ((U.lift 1).le_opNorm x |>.trans
    (by simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg (U.lift 1))))

/-- Separate witnesses for arbitrarily large coordinate weights exclude an
actual strong propagator. No sequence of witness vectors is selected. -/
theorem no_strongPropagator_of_unbounded_swap_coordinates
    (domain : CommonDomain D E) (H : D →L[ℂ] E)
    (hwitness : ∀ n : ℕ, ∃ a b : E →L[ℂ] ℂ,
      (∀ d : D, a (H d) = b (domain.inclusion d)) ∧
      (∀ d : D, b (H d) = a (domain.inclusion d)) ∧
      ∃ x : D, a (domain.inclusion x) = 1 ∧ b (domain.inclusion x) = 0 ∧
        ‖x‖ ≤ 1 ∧ ∀ d : D, (n : ℝ) * ‖b (domain.inclusion d)‖ ≤ ‖d‖) :
    ¬ Nonempty (StrongPropagator domain (fun _ => H) (fun _ => 0)
      (-Complex.I * (Real.pi / 2 : ℝ))) := by
  rintro ⟨U⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖U.lift 1‖
  obtain ⟨a, b, ha, hb, x, hax, hbx, hx, hw⟩ := hwitness n
  exact (not_le_of_gt hn)
    (strongPropagator_swap_lift_norm_lower domain H U a b ha hb x hax hbx hx n hw)

end Adiabatic.Foundations
