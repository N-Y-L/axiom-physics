import Adiabatic.Infinite.RieszCommutator
import Adiabatic.Infinite.CommutatorTheorem

/-!
# Quantum adiabatic theorem in arbitrary dimension with a fixed spectral contour

A twice continuously differentiable bounded self-adjoint Hamiltonian and a
fixed circle in its resolvent set determine a smooth orthogonal spectral
projection. The resolvent contour constructs the commutator solution, and the
Schrödinger and Kato propagators are constructed from their equations.

The resulting operator-norm leakage bound is uniform in time and is `C / T`,
with the constant chosen before the runtime. There is no dimension or rank
assumption. The same fixed isolating circle is required at every time.
-/

noncomputable section

namespace Adiabatic.Infinite

open Set Metric

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
/-- A fixed resolvent contour supplies the C¹ Kato commutator solution. -/
theorem exists_contDiffOn_contour_commutator {H : ℝ → A} {s : Set ℝ}
    (hH : ContDiffOn ℝ 2 H s) (hs : UniqueDiffOn ℝ s) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ t ∈ s, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    ∃ X : ℝ → A, ContDiffOn ℝ 1 X s ∧ ∀ t ∈ s,
      H t * X t - X t * H t = katoGenerator (rieszProjection (H t) c r)
        (derivWithin (fun u => rieszProjection (H u) c r) s t) := by
  let P : ℝ → A := fun t => rieszProjection (H t) c r
  have hp : ContDiffOn ℝ 2 P s := contDiffOn_rieszProjection hH hr hgap
  have hd : ContDiffOn ℝ 1 (derivWithin P s) s := hp.derivWithin hs (by norm_num)
  refine ⟨fun t => contourCommutator (H t) (derivWithin P s t) c r hr,
    contDiffOn_contourCommutator (hH.of_le (by norm_num)) hd hr hgap, ?_⟩
  intro t ht
  exact contourCommutator_commutator _ hr (hgap t ht)

/-- A bounded Hamiltonian with a fixed isolating circle obeys a uniform
adiabatic leakage estimate, with its spectral projection constructed internally. -/
theorem bounded_adiabatic_estimate_of_resolvent_contour
    (H : ℝ → A) (hH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hHstar : ∀ t ∈ Icc (0 : ℝ) 1, IsSelfAdjoint (H t))
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ U : ℝ → A,
      U 0 = 1 →
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(1 - rieszProjection (H t) c r) * U t * rieszProjection (H 0) c r‖ ≤ C / T := by
  let interval : Set ℝ := Icc 0 1
  have hs : UniqueDiffOn ℝ interval := uniqueDiffOn_Icc zero_lt_one
  let P : ℝ → A := fun t => rieszProjection (H t) c r
  have hp : ContDiffOn ℝ 2 P interval := contDiffOn_rieszProjection hH hr.le hgap
  obtain ⟨X, hx, hcomm⟩ := exists_contDiffOn_contour_commutator hH hs hr.le hgap
  have hprojection (t : ℝ) (ht : t ∈ interval) : P t * P t = P t ∧ star (P t) = P t :=
    rieszProjection_isStarProjection (hHstar t ht).isStarNormal hr (hgap t ht)
  exact exists_adiabatic_bound_of_commutator H P (derivWithin P interval) X
    (derivWithin X interval) hH.continuousOn
    (hp.derivWithin hs (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuousOn
    hx.continuousOn (hx.continuousOn_derivWithin hs (by rfl))
    (fun t ht => (hHstar t ht).star_eq) (fun t ht => (hprojection t ht).2)
    (fun t ht => (hprojection t ht).1)
    (fun t ht => (rieszProjection_commute (hHstar t ht).isStarNormal hr (hgap t ht)).eq.symm)
    (fun t ht => ((hp.differentiableOn (by norm_num)) t ht).hasDerivWithinAt)
    (fun t ht => ((hx.differentiableOn (by norm_num)) t ht).hasDerivWithinAt) hcomm

/-- The bounded spectral-gap theorem in arbitrary dimension: unitary
Schrödinger propagators and a uniform `C / T` estimate for every solution. -/
theorem bounded_adiabatic_theorem_of_resolvent_contour
    (H : ℝ → A) (hH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hHstar : ∀ t ∈ Icc (0 : ℝ) 1, IsSelfAdjoint (H t))
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c r, z ∉ spectrum ℂ (H t)) :
    (∀ T : ℝ, ∃ U : ℝ → A, U 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, U t ∈ unitary A) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ U : ℝ → A,
      U 0 = 1 →
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt U ((-Complex.I * (T : ℂ)) • (H t * U t)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(1 - rieszProjection (H t) c r) * U t * rieszProjection (H 0) c r‖ ≤ C / T := by
  exact ⟨fun T => exists_unitary_schrodinger_propagator H hH.continuousOn
    (fun t ht => (hHstar t ht).star_eq) T,
    bounded_adiabatic_estimate_of_resolvent_contour H hH hHstar c r hr hgap⟩

end Adiabatic.Infinite
