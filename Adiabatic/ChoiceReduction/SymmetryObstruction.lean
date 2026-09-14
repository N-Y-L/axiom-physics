import Lean

/-!
# A symmetry obstruction to extracting a choice from a pair

An equivariant map preserves fixed points. Consequently, canonical data that
are fixed by exchanging the two coordinates cannot produce an oriented pair.
These elementary lemmas isolate that obstruction without assuming linearity,
completeness, a spectral theorem, or a choice principle.

This file is an independent research implementation. It does not assert that
an arbitrary Hamiltonian is equivariant, or that every choice construction is
equivariant.
-/

namespace Adiabatic.ChoiceReduction

universe u v

theorem equivariant_map_preserves_fixed_point
    {X : Type u} {Y : Type v} (s : X → X) (t : Y → Y)
    (f : X → Y) (hf : ∀ x, f (s x) = t (f x))
    (x : X) (hx : s x = x) : t (f x) = f x := by
  exact (hf x).symm.trans (congrArg f hx)

theorem no_equivariant_map_to_fixed_point_free_action
    {X : Type u} {Y : Type v} (s : X → X) (t : Y → Y)
    (f : X → Y) (hf : ∀ x, f (s x) = t (f x))
    (x : X) (hx : s x = x) (ht : ∀ y, t y ≠ y) : False := by
  exact ht (f x) (equivariant_map_preserves_fixed_point s t f hf x hx)

def flipPairCoordinates {α : Type u} (v : Bool → α) : Bool → α :=
  fun b => v (!b)

theorem flipPairCoordinates_constant {α : Type u} (a : α) :
    flipPairCoordinates (fun _ => a) = (fun _ => a) := rfl

theorem equivariant_pair_map_equal_coordinates
    {α : Type u} {β : Type v}
    (F : (Bool → α) → (Bool → β))
    (hF : ∀ x, F (flipPairCoordinates x) = flipPairCoordinates (F x))
    (a : α) : F (fun _ => a) false = F (fun _ => a) true := by
  have h := equivariant_map_preserves_fixed_point
    flipPairCoordinates flipPairCoordinates F hF (fun _ => a) rfl
  exact (congrArg (fun w : Bool → β => w false) h).symm

theorem bool_not_has_no_fixed_point (b : Bool) : (!b) ≠ b := by
  cases b <;> intro h <;> cases h

theorem no_equivariant_pair_selector
    {α : Type u} (a : α) (select : (Bool → α) → Bool)
    (hselect : ∀ x, select (flipPairCoordinates x) = !(select x)) : False := by
  exact no_equivariant_map_to_fixed_point_free_action
    flipPairCoordinates Bool.not select hselect (fun _ => a) rfl
    bool_not_has_no_fixed_point

/-- The coefficient hypothesis holds for negation on a complex vector space.
The abstract form avoids importing analytic APIs into the symmetry lemma. -/
theorem equivariant_antisymmetric_pair_output_zero
    {α : Type u} {β : Type v}
    (F : (Bool → α) → (Bool → β))
    (hF : ∀ x, F (flipPairCoordinates x) = flipPairCoordinates (F x))
    (a : α) (neg : β → β) (zero : β)
    (hneg : ∀ b, neg b = b → b = zero)
    (hanti : F (fun _ => a) true = neg (F (fun _ => a) false)) :
    ∀ b, F (fun _ => a) b = zero := by
  have heq := equivariant_pair_map_equal_coordinates F hF a
  have hz := hneg (F (fun _ => a) false) (hanti.symm.trans heq.symm)
  intro b
  cases b
  · exact hz
  · exact heq.symm.trans hz

/-- Conjugation invariance of a uniquely specified solution follows from
closure of its defining predicate under conjugation. Analytic applications
must separately prove that closure hypothesis. -/
theorem unique_solution_fixed_by_symmetry
    {S : Type u} (isSolution : S → Prop) (symmetry : S → S)
    (solution : S) (hsolution : isSolution solution)
    (hunique : ∀ s, isSolution s → s = solution)
    (hclosed : ∀ s, isSolution s → isSolution (symmetry s)) :
    symmetry solution = solution := by
  exact hunique (symmetry solution) (hclosed solution hsolution)

end Adiabatic.ChoiceReduction
