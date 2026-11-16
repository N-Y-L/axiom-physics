import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Calculus for strongly differentiable operator curves

Unbounded Hamiltonians generally produce evolution that is differentiable
only after application to a vector in their domain. The product rule here
uses strong convergence and a local uniform operator bound. It does not
assume operator-norm differentiability of the evolution.
-/

namespace Adiabatic.Unbounded

open Filter Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Real-time product differentiation of complex-linear operator curves. -/
theorem hasDerivWithinAt_apply
    {A : ℝ → E →L[ℂ] F} {A' : E →L[ℂ] F} {v : ℝ → E} {v' : E}
    {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun u => A u (v u)) (A' (v t) + A t v') s t := by
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).hasFDerivAt
    |>.comp_hasDerivWithinAt t hA
  exact hr.clm_apply hv

/-- Uniformly bounded operators may be applied to a convergent varying vector
when they converge strongly on its limit. -/
theorem tendsto_apply_of_strong {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℂ] F} {v : ι → E} {v₀ : E} {w : F} {M : ℝ}
    (hbound : ∀ᶠ i in l, ‖A i‖ ≤ M)
    (hA : Tendsto (fun i => A i v₀) l (𝓝 w))
    (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => A i (v i)) l (𝓝 w) := by
  have hsmall : Tendsto (fun i => A i (v i - v₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun i => M * ‖v i - v₀‖)
    · filter_upwards [hbound] with i hi
      exact (A i).le_opNorm (v i - v₀) |>.trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa using ((hv.sub_const v₀).norm.const_mul M)
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add hA

/-- Strong product rule. Only the fixed vector `v t` needs an operator
derivative; strong continuity is needed on the derivative vector `v'`. -/
theorem hasDerivWithinAt_apply_of_strong
    {A : ℝ → E →L[ℂ] F} {v : ℝ → E} {v' : E} {w : F}
    {s : Set ℝ} {t M : ℝ}
    (hbound : ∀ᶠ u in 𝓝[s] t, ‖A u‖ ≤ M)
    (hA : ContinuousWithinAt (fun u => A u v') s t)
    (hfixed : HasDerivWithinAt (fun u => A u (v t)) w s t)
    (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun u => A u (v u)) (A t v' + w) s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hv hfixed ⊢
  have hmono : 𝓝[s \ {t}] t ≤ 𝓝[s] t := nhdsWithin_mono t diff_subset
  have hfirst := tendsto_apply_of_strong
    (hbound.filter_mono hmono) (hA.mono_left hmono) hv
  convert hfirst.add hfixed using 1
  ext u
  simp only [slope_def_module, ContinuousLinearMap.map_smul_of_tower, map_sub, smul_sub]
  abel

/-- Strong continuity passes to uniformly bounded inverses. -/
theorem continuousWithinAt_inverse_apply_of_strong
    {A : ℝ → E →L[ℂ] F} {B : ℝ → F →L[ℂ] E} {x : F}
    {s : Set ℝ} {t M : ℝ}
    (hbound : ∀ᶠ u in 𝓝[s] t, ‖B u‖ ≤ M)
    (hleft : ∀ᶠ u in 𝓝[s] t, ∀ y, B u (A u y) = y)
    (hright : A t (B t x) = x)
    (hA : ContinuousWithinAt (fun u => A u (B t x)) s t) :
    ContinuousWithinAt (fun u => B u x) s t := by
  have hz : Tendsto (fun u => B u (A u (B t x) - A t (B t x)))
      (𝓝[s] t) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u => M * ‖A u (B t x) - A t (B t x)‖)
    · filter_upwards [hbound] with u hu
      exact ((B u).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
    · simpa using (hA.sub_const (A t (B t x))).norm.const_mul M
  have heq : (fun u => B u x) =ᶠ[𝓝[s] t]
      (fun u => B t x - B u (A u (B t x) - A t (B t x))) := by
    filter_upwards [hleft] with u hu
    simp only [map_sub, hu, hright]
    abel
  simpa only [sub_zero] using
    ((tendsto_const_nhds (x := B t x)).sub hz).congr' heq.symm

/-- Strong differentiation of inverse operators on a fixed vector.
The derivative of the original curve is only required at `B t x`. -/
theorem hasDerivWithinAt_inverse_apply_of_strong
    {A : ℝ → E →L[ℂ] F} {B : ℝ → F →L[ℂ] E} {x w : F}
    {s : Set ℝ} {t M : ℝ}
    (hbound : ∀ᶠ u in 𝓝[s] t, ‖B u‖ ≤ M)
    (hleft : ∀ᶠ u in 𝓝[s] t, ∀ y, B u (A u y) = y)
    (hright : A t (B t x) = x)
    (hB : ContinuousWithinAt (fun u => B u w) s t)
    (hA : HasDerivWithinAt (fun u => A u (B t x)) w s t) :
    HasDerivWithinAt (fun u => B u x) (-B t w) s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hA ⊢
  have hmono : 𝓝[s \ {t}] t ≤ 𝓝[s] t := nhdsWithin_mono t diff_subset
  have hlim := (tendsto_apply_of_strong
    (hbound.filter_mono hmono) (hB.mono_left hmono) hA).neg
  apply hlim.congr'
  filter_upwards [hleft.filter_mono hmono] with u hu
  simp only [slope_def_module, ContinuousLinearMap.map_smul_of_tower,
    map_sub, hu, hright, smul_sub]
  abel

end Adiabatic.Unbounded
