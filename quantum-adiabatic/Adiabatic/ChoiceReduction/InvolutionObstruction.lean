import Mathlib.Algebra.Group.Hom.Basic

/-!
# Fixed points of two additive involutions

If two additive involutions each have only the zero fixed point, both are
negation and their composite is the identity. This obstructs an equivariant
selector defined on every nonzero vector for two independent pair flips.
It does not rule out selecting from vectors with an additional property.
-/

namespace Adiabatic.ChoiceReduction

variable {V : Type*} [AddCommGroup V]

theorem involution_eq_neg_of_trivial_fixed_points
    (A : V →+ V) (hA : ∀ x, A (A x) = x)
    (hfixed : ∀ x, A x = x → x = 0) (x : V) : A x = -x := by
  have hz : x + A x = 0 := hfixed (x + A x) (by
    rw [map_add, hA, add_comm])
  exact eq_neg_of_add_eq_zero_right hz

theorem involutions_comp_eq_self_of_trivial_fixed_points
    (A B : V →+ V) (hA : ∀ x, A (A x) = x) (hB : ∀ x, B (B x) = x)
    (hfixedA : ∀ x, A x = x → x = 0)
    (hfixedB : ∀ x, B x = x → x = 0) (x : V) : A (B x) = x := by
  rw [involution_eq_neg_of_trivial_fixed_points B hB hfixedB,
    map_neg, involution_eq_neg_of_trivial_fixed_points A hA hfixedA, neg_neg]

theorem trivial_of_three_trivial_fixed_spaces
    (A B : V →+ V) (hA : ∀ x, A (A x) = x) (hB : ∀ x, B (B x) = x)
    (hfixedA : ∀ x, A x = x → x = 0)
    (hfixedB : ∀ x, B x = x → x = 0)
    (hfixedAB : ∀ x, A (B x) = x → x = 0) : ∀ x : V, x = 0 := by
  intro x
  exact hfixedAB x
    (involutions_comp_eq_self_of_trivial_fixed_points A B hA hB hfixedA hfixedB x)

/-- A selector on nonzero vectors cannot preserve two pair flips when each
flip and their composite have no fixed points in the target. Commutation is
not needed for this obstruction. The selector is supplied only on nonzero
vectors, and decidable equality is supplied for the zero case split. No choice
function is constructed or assumed on arbitrary sets. -/
theorem no_equivariant_nonzero_selector_for_two_involutions
    [DecidableEq V] {Y : Type*} (A B : V →+ V) (hA : ∀ x, A (A x) = x)
    (hB : ∀ x, B (B x) = x) (a b : Y → Y)
    (select : ∀ x : V, x ≠ 0 → Y)
    (equivA : ∀ x hx hAx, select (A x) hAx = a (select x hx))
    (equivB : ∀ x hx hBx, select (B x) hBx = b (select x hx))
    (freeA : ∀ y, a y ≠ y) (freeB : ∀ y, b y ≠ y)
    (freeAB : ∀ y, a (b y) ≠ y) (x : V) (hx : x ≠ 0) : False := by
  have nonzeroA : ∀ z, z ≠ 0 → A z ≠ 0 := by
    intro z hz hzero
    apply hz
    calc z = A (A z) := (hA z).symm
         _ = 0 := by rw [hzero, map_zero]
  have nonzeroB : ∀ z, z ≠ 0 → B z ≠ 0 := by
    intro z hz hzero
    apply hz
    calc z = B (B z) := (hB z).symm
         _ = 0 := by rw [hzero, map_zero]
  have fixedA : ∀ z, A z = z → z = 0 := by
    intro z hfix
    by_cases hz : z = 0
    · exact hz
    · have heq := equivA z hz (nonzeroA z hz)
      have hs : select (A z) (nonzeroA z hz) = select z hz :=
        congrArg (fun v : {w : V // w ≠ 0} => select v.1 v.2)
          (show (⟨A z, nonzeroA z hz⟩ : {w : V // w ≠ 0}) = ⟨z, hz⟩ from Subtype.ext hfix)
      exact False.elim (freeA (select z hz) (heq.symm.trans hs))
  have fixedB : ∀ z, B z = z → z = 0 := by
    intro z hfix
    by_cases hz : z = 0
    · exact hz
    · have heq := equivB z hz (nonzeroB z hz)
      have hs : select (B z) (nonzeroB z hz) = select z hz :=
        congrArg (fun v : {w : V // w ≠ 0} => select v.1 v.2)
          (show (⟨B z, nonzeroB z hz⟩ : {w : V // w ≠ 0}) = ⟨z, hz⟩ from Subtype.ext hfix)
      exact False.elim (freeB (select z hz) (heq.symm.trans hs))
  have hab := involutions_comp_eq_self_of_trivial_fixed_points A B hA hB fixedA fixedB x
  have heq := equivA (B x) (nonzeroB x hx) (nonzeroA (B x) (nonzeroB x hx))
  rw [equivB x hx (nonzeroB x hx)] at heq
  have hs : select (A (B x)) (nonzeroA (B x) (nonzeroB x hx)) = select x hx :=
    congrArg (fun v : {w : V // w ≠ 0} => select v.1 v.2)
      (show (⟨A (B x), nonzeroA (B x) (nonzeroB x hx)⟩ : {w : V // w ≠ 0}) = ⟨x, hx⟩
        from Subtype.ext hab)
  exact freeAB (select x hx) (heq.symm.trans hs)

end Adiabatic.ChoiceReduction
