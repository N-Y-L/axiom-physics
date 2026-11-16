import Mathlib.Data.Fin.Basic

/-!
# Finite simultaneous existential witnesses

Existential witnesses indexed by an explicit finite set can be combined by
induction. The result remains an existence proposition; no arbitrary choice
function is extracted. This can replace a use of choice after a finite
family of local problems has been specified. It does not produce a finite
cover from compactness or select a witness over an infinite index set.
-/

namespace Adiabatic.ChoiceReduction

/-- A finite dependent family of existential statements has simultaneous witnesses. -/
theorem exists_fin_selection (n : ℕ) :
    ∀ (B : Fin n → Type*) (p : ∀ i, B i → Prop),
      (∀ i, ∃ x, p i x) → ∃ f : ∀ i, B i, ∀ i, p i (f i) := by
  induction n with
  | zero =>
      intro B p _
      exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro B p h
      obtain ⟨x, hx⟩ := h 0
      obtain ⟨f, hf⟩ := ih (fun i => B i.succ) (fun i => p i.succ) (fun i => h i.succ)
      refine ⟨Fin.cases x f, ?_⟩
      intro i
      exact Fin.cases hx hf i

/-- A finite family of nondependent existential statements has simultaneous witnesses. -/
theorem exists_fin_function {B : Type*} {n : ℕ} (p : Fin n → B → Prop)
    (h : ∀ i, ∃ x, p i x) : ∃ f : Fin n → B, ∀ i, p i (f i) :=
  exists_fin_selection n (fun _ => B) p h

end Adiabatic.ChoiceReduction
