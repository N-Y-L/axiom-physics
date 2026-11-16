import Adiabatic.Foundations.StrongSwapObstruction
import Adiabatic.Foundations.SwapExtraction

/-!
# Bounded inverses extracted from actual swap evolution

The scalar swap equation is solved for arbitrary initial coordinates.
Testing Hilbert-valued coordinates against individual vectors then identifies
the quarter-turn action of an actual `StrongPropagator`. For a product domain,
this supplies the lift identity needed to extract a bounded inverse.

The final theorem assumes a genuine propagator and explicit coordinate maps;
it does not assume the inverse or the quarter-turn lift identity. Construction
of the doubled gapped Hamiltonian and the ZF interpretation remain separate.
-/

namespace Adiabatic.Foundations

open Set Adiabatic.Unbounded

/-- The scalar swap equation exchanges arbitrary initial values at a quarter turn. -/
theorem swap_quarter_turn_values (f g : ℝ → ℂ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt f ((-Complex.I * (Real.pi / 2 : ℝ)) * g t) (Icc 0 1) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((-Complex.I * (Real.pi / 2 : ℝ)) * f t) (Icc 0 1) t) :
    f 1 = -Complex.I * g 0 ∧ g 1 = -Complex.I * f 0 := by
  let c : ℂ := -Complex.I * (Real.pi / 2 : ℝ)
  have hp := scalar_integrating_factor (fun t => f t + g t) c
    (fun t ht => by
      convert (hf t ht).add (hg t ht) using 1
      dsimp [c]
      ring)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hm := scalar_integrating_factor (fun t => f t - g t) (-c)
    (fun t ht => by
      convert (hf t ht).sub (hg t ht) using 1
      dsimp [c]
      ring)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hep : Complex.exp (-c) = Complex.I := by
    have hc : -c = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by dsimp [c]; ring
    rw [hc, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  have hem : Complex.exp c = -Complex.I := by
    rw [← neg_neg c, Complex.exp_neg, hep]
    simp
  simp only [Complex.ofReal_one, neg_mul, one_mul] at hp hm
  rw [hep] at hp
  simp only [neg_neg] at hm
  rw [hem] at hm
  have hplus : f 1 + g 1 = -Complex.I * (f 0 + g 0) := by
    calc
      f 1 + g 1 = -Complex.I * (Complex.I * (f 1 + g 1)) := by simp [← mul_assoc]
      _ = -Complex.I * (f 0 + g 0) := by rw [hp]
  have hminus : f 1 - g 1 = Complex.I * (f 0 - g 0) := by
    calc
      f 1 - g 1 = Complex.I * (-Complex.I * (f 1 - g 1)) := by simp [← mul_assoc]
      _ = Complex.I * (f 0 - g 0) := by rw [hm]
  constructor
  · linear_combination (hplus + hminus) / 2
  · linear_combination (hplus - hminus) / 2

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Hilbert-valued coordinates of an actual swap propagator have the forced
quarter-turn values. Each inner-product test is considered separately. -/
theorem strongPropagator_swap_coordinate_maps (domain : CommonDomain D F)
    (H : D →L[ℂ] F)
    (U : StrongPropagator domain (fun _ => H) (fun _ => 0)
      (-Complex.I * (Real.pi / 2 : ℝ)))
    (a b : F →L[ℂ] E)
    (ha : ∀ d : D, a (H d) = b (domain.inclusion d))
    (hb : ∀ d : D, b (H d) = a (domain.inclusion d)) (x : D) :
    a (domain.inclusion (U.lift 1 x)) = -Complex.I • b (domain.inclusion x) ∧
      b (domain.inclusion (U.lift 1 x)) = -Complex.I • a (domain.inclusion x) := by
  have htest (v : E) :
      inner ℂ v (a (domain.inclusion (U.lift 1 x))) =
        -Complex.I * inner ℂ v (b (domain.inclusion x)) ∧
      inner ℂ v (b (domain.inclusion (U.lift 1 x))) =
        -Complex.I * inner ℂ v (a (domain.inclusion x)) := by
    let av : F →L[ℂ] ℂ := (innerSL ℂ v).comp a
    let bv : F →L[ℂ] ℂ := (innerSL ℂ v).comp b
    let f : ℝ → ℂ := fun t => av (U.evolution t (domain.inclusion x))
    let g : ℝ → ℂ := fun t => bv (U.evolution t (domain.inclusion x))
    have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivWithinAt f ((-Complex.I * (Real.pi / 2 : ℝ)) * g t) (Icc 0 1) t := by
      have hd := (av.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (U.strong_derivative x t ht)
      simpa [f, g, av, bv, ha, U.preserves_domain t ht, inner_smul_right] using hd
    have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivWithinAt g ((-Complex.I * (Real.pi / 2 : ℝ)) * f t) (Icc 0 1) t := by
      have hd := (bv.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (U.strong_derivative x t ht)
      simpa [f, g, av, bv, hb, U.preserves_domain t ht, inner_smul_right] using hd
    have hvalues := swap_quarter_turn_values f g hf hg
    have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simpa [f, g, av, bv, U.initial, U.preserves_domain 1 ht] using hvalues
  constructor
  · apply ext_inner_left ℂ
    intro v
    simpa [inner_smul_right] using (htest v).1
  · apply ext_inner_left ℂ
    intro v
    simpa [inner_smul_right] using (htest v).2

/-- An actual strong swap propagator on a product domain supplies a bounded
inverse of the original inclusion. No inverse or lift action is assumed. -/
theorem bounded_inverse_of_strong_swap
    (j : D →L[ℂ] E) (hj : Function.Injective j)
    (domain : CommonDomain (D × E) F) (H : (D × E) →L[ℂ] F)
    (U : StrongPropagator domain (fun _ => H) (fun _ => 0)
      (-Complex.I * (Real.pi / 2 : ℝ)))
    (a b : F →L[ℂ] E)
    (ha_domain : ∀ d : D × E, a (domain.inclusion d) = j d.1)
    (hb_domain : ∀ d : D × E, b (domain.inclusion d) = d.2)
    (ha : ∀ d : D × E, a (H d) = b (domain.inclusion d))
    (hb : ∀ d : D × E, b (H d) = a (domain.inclusion d)) :
    ∃ R : E →L[ℂ] D, (∀ y, j (R y) = y) ∧ (∀ x, R (j x) = x) := by
  apply bounded_inverse_of_swap_lift j hj (U.lift 1)
  intro y
  have h := (strongPropagator_swap_coordinate_maps domain H U a b ha hb (0, y)).1
  simpa [ha_domain, hb_domain] using h

end Adiabatic.Foundations
