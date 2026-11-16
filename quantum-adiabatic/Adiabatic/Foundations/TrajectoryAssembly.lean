import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Coherence of individually specified Schrödinger trajectories

Symmetry and the strong equation imply preservation of inner products and
uniqueness for domain-valued trajectories. An explicitly supplied family of
normalized trajectories is consequently linear in its initial state and
bounded into the physical norm. Existence of the trajectories is an input;
this file does not construct the propagator of the common-domain theorem.

The proofs introduce no selector of trajectories. Their full mathlib axiom
dependencies must still be audited; this is not a choice-free model of ZF.
-/

namespace Adiabatic.Foundations

open Set

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two domain trajectories for the same symmetric generator preserve their
physical inner product. Completeness and domain-norm estimates are unnecessary. -/
theorem domainTrajectory_inner_constant (j : D →L[ℂ] E)
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (f g : ℝ → D)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (f s)) (z • H t (f t)) (Icc 0 1) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (g s)) (z • H t (g t)) (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    inner ℂ (j (f t)) (j (g t)) = inner ℂ (j (f 0)) (j (g 0)) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => inner ℂ (j (f r)) (j (g r)))
        0 (Icc 0 1) s := by
    convert (hf s hs).inner ℂ (hg s hs) using 1
    rw [inner_smul_right, inner_smul_left, hH s hs]
    change 0 = z * inner ℂ (j (f s)) (H s (g s)) +
      star z * inner ℂ (j (f s)) (H s (g s))
    rw [hz]
    ring
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun s hs => le_refl (‖(0 : ℂ)‖)) (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ht
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa using hb) (norm_nonneg _)))

/-- An individual strong trajectory preserves its physical norm. -/
theorem domainTrajectory_norm_constant (j : D →L[ℂ] E)
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (f : ℝ → D)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (f s)) (z • H t (f t)) (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖j (f t)‖ = ‖j (f 0)‖ := by
  have h := congrArg Complex.re
    (domainTrajectory_inner_constant j H hH z hz f f hf hf ht)
  rw [show (inner ℂ (j (f t)) (j (f t))).re = ‖j (f t)‖ ^ 2 from
      @inner_self_eq_norm_sq ℂ E _ _ _ _,
    show (inner ℂ (j (f 0)) (j (f 0))).re = ‖j (f 0)‖ ^ 2 from
      @inner_self_eq_norm_sq ℂ E _ _ _ _] at h
  nlinarith [norm_nonneg (j (f t)), norm_nonneg (j (f 0))]

/-- Uniqueness on the domain follows from the physical energy identity and
injectivity of the inclusion, without assuming a bounded domain lift. -/
theorem domainTrajectory_unique (j : D →L[ℂ] E) (hj : Function.Injective j)
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (f g : ℝ → D)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (f s)) (z • H t (f t)) (Icc 0 1) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (g s)) (z • H t (g t)) (Icc 0 1) t)
    (hzero : f 0 = g 0) : EqOn f g (Icc (0 : ℝ) 1) := by
  intro t ht
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => j (f r - g r))
        (z • H s (f s - g s)) (Icc 0 1) s := by
    simpa only [map_sub, smul_sub] using (hf s hs).sub (hg s hs)
  have hn := domainTrajectory_norm_constant j H hH z hz (fun r => f r - g r) hd ht
  apply hj
  exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [hzero] using hn))

/-- Additivity in the initial state is forced for any explicitly supplied
family of normalized domain trajectories. It is not an extra hypothesis. -/
theorem domainTrajectory_family_add (j : D →L[ℂ] E) (hj : Function.Injective j)
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (F : D → ℝ → D)
    (hzero : ∀ x, F x 0 = x)
    (hF : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (F x s)) (z • H t (F x t)) (Icc 0 1) t)
    (x y : D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F (x + y) t = F x t + F y t := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => j (F x r + F y r))
        (z • H s (F x s + F y s)) (Icc 0 1) s := by
    simpa only [map_add, smul_add] using (hF x s hs).add (hF y s hs)
  exact domainTrajectory_unique j hj H hH z hz (F (x + y))
    (fun r => F x r + F y r) (hF (x + y)) hd (by simp only [hzero]) ht

/-- Scalar linearity is also forced by the differential equation. -/
theorem domainTrajectory_family_smul (j : D →L[ℂ] E) (hj : Function.Injective j)
    (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (F : D → ℝ → D)
    (hzero : ∀ x, F x 0 = x)
    (hF : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (F x s)) (z • H t (F x t)) (Icc 0 1) t)
    (c : ℂ) (x : D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F (c • x) t = c • F x t := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => j (c • F x r))
        (z • H s (c • F x s)) (Icc 0 1) s := by
    simpa only [map_smul, smul_smul, mul_comm z c] using (hF x s hs).const_smul c
  exact domainTrajectory_unique j hj H hH z hz (F (c • x))
    (fun r => c • F x r) (hF (c • x)) hd (by simp only [hzero]) ht

/-- A supplied trajectory family canonically yields a bounded linear physical
map at each time. This proves neither the existence of that family nor a
bound in the supplied domain norm. -/
noncomputable def domainTrajectory_physicalMap (j : D →L[ℂ] E)
    (hj : Function.Injective j) (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (F : D → ℝ → D)
    (hzero : ∀ x, F x 0 = x)
    (hF : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (F x s)) (z • H t (F x t)) (Icc 0 1) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : D →L[ℂ] E :=
  let L : D →ₗ[ℂ] E :=
    { toFun := fun x => j (F x t)
      map_add' := fun x y => by
        rw [domainTrajectory_family_add j hj H hH z hz F hzero hF x y ht, map_add]
      map_smul' := fun c x => by
        rw [domainTrajectory_family_smul j hj H hH z hz F hzero hF c x ht, map_smul]
        rfl }
  L.mkContinuous ‖j‖ (fun x => by
    change ‖j (F x t)‖ ≤ ‖j‖ * ‖x‖
    rw [domainTrajectory_norm_constant j H hH z hz (F x) (hF x) ht, hzero]
    exact j.le_opNorm x)

/-- The assembled map agrees with the given trajectory by definition. -/
theorem domainTrajectory_physicalMap_apply (j : D →L[ℂ] E)
    (hj : Function.Injective j) (H : ℝ → D →L[ℂ] E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      inner ℂ (H t x) (j y) = inner ℂ (j x) (H t y))
    (z : ℂ) (hz : star z = -z) (F : D → ℝ → D)
    (hzero : ∀ x, F x 0 = x)
    (hF : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => j (F x s)) (z • H t (F x t)) (Icc 0 1) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : D) :
    domainTrajectory_physicalMap j hj H hH z hz F hzero hF t ht x = j (F x t) := rfl

end Adiabatic.Foundations
