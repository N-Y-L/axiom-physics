import Mathlib.Logic.Function.Basic

/-!
# Selection principles and right inverses

For arbitrary maps, splitting every surjection is equivalent to the
propositional axiom of choice for dependent families. A uniform construction
of those sections also extracts elements from arbitrary nonempty types.
For bijections the corresponding construction needs only unique-witness
extraction. These are conditional equivalences of general selection
principles. No implication from the adiabatic theorem to any of these
principles is asserted here.
-/

namespace Adiabatic.ChoiceReduction

universe u

/-- The propositional axiom of choice for families in one universe. -/
def FamilyChoice : Prop :=
  ∀ (I : Type u) (B : I → Type u), (∀ i, Nonempty (B i)) → Nonempty (∀ i, B i)

/-- Every surjective map between types in one universe has a right inverse. -/
def SurjectionSplitting : Prop :=
  ∀ (A B : Type u) (f : A → B), Function.Surjective f →
    ∃ g : B → A, Function.RightInverse g f

/-- Choice for dependent families supplies right inverses of surjections by
selecting an element of each fiber. -/
theorem FamilyChoice.surjectionSplitting (h : FamilyChoice.{u}) :
    SurjectionSplitting.{u} := by
  intro A B f hf
  have fibers : ∀ b, Nonempty {a : A // f a = b} := by
    intro b
    obtain ⟨a, ha⟩ := hf b
    exact ⟨⟨a, ha⟩⟩
  obtain ⟨s⟩ := h B (fun b => {a : A // f a = b}) fibers
  exact ⟨fun b => (s b).val, fun b => (s b).property⟩

/-- A right inverse of the total-space projection selects one element in
each inhabited fiber. Thus arbitrary surjection splitting implies choice. -/
theorem SurjectionSplitting.familyChoice (h : SurjectionSplitting.{u}) :
    FamilyChoice.{u} := by
  intro I B inhabited
  have projection_surjective : Function.Surjective (@Sigma.fst I B) := by
    intro i
    obtain ⟨x⟩ := inhabited i
    exact ⟨⟨i, x⟩, rfl⟩
  obtain ⟨s, hs⟩ := h (Sigma B) I Sigma.fst projection_surjective
  exact ⟨fun i => (hs i) ▸ (s i).snd⟩

/-- Arbitrary surjection splitting and propositional family choice are equivalent. -/
theorem familyChoice_iff_surjectionSplitting :
    FamilyChoice.{u} ↔ SurjectionSplitting.{u} :=
  ⟨FamilyChoice.surjectionSplitting, SurjectionSplitting.familyChoice⟩

/-- A uniform operation extracting an element from every nonempty type.
This has the type of a choice operation, rather than merely asserting
propositional existence of a function for each family. -/
def NonemptySelector : Type (u + 1) := ∀ A : Type u, Nonempty A → A

/-- A uniform operation supplying a right inverse for each surjection. -/
def SurjectionSectionSelector : Type (u + 1) :=
  ∀ (A B : Type u) (f : A → B), Function.Surjective f →
    {g : B → A // Function.RightInverse g f}

/-- An element selector constructs sections by selecting in the fibers. -/
def NonemptySelector.surjectionSections (select : NonemptySelector.{u}) :
    SurjectionSectionSelector.{u} :=
  fun A B f hf =>
    let fiber : ∀ b, {a : A // f a = b} := fun b =>
      select {a : A // f a = b} (by
        obtain ⟨a, ha⟩ := hf b
        exact ⟨⟨a, ha⟩⟩)
    ⟨fun b => (fiber b).val, fun b => (fiber b).property⟩

/-- A uniform section construction contains a choice operation: apply it to
the map from an arbitrary nonempty type to the singleton type. -/
def SurjectionSectionSelector.nonemptySelector
    (sections : SurjectionSectionSelector.{u}) : NonemptySelector.{u} :=
  fun A inhabited =>
    let f : A → PUnit.{u + 1} := fun _ => PUnit.unit
    let onto : Function.Surjective f := by
      intro b
      obtain ⟨a⟩ := inhabited
      exact ⟨a, by cases b; rfl⟩
    (sections A PUnit f onto).val PUnit.unit

/-- The data-level forms of arbitrary selection and surjection splitting
are equivalent in inhabitation. -/
theorem nonemptySelector_iff_surjectionSections :
    Nonempty (NonemptySelector.{u}) ↔ Nonempty (SurjectionSectionSelector.{u}) := by
  constructor
  · intro h
    obtain ⟨select⟩ := h
    exact ⟨select.surjectionSections⟩
  · intro h
    obtain ⟨sections⟩ := h
    exact ⟨sections.nonemptySelector⟩

/-- A uniform operation extracting a witness from unique existence. -/
def UniqueWitnessSelector : Type (u + 1) :=
  ∀ (A : Type u) (p : A → Prop), (∃! a, p a) → {a : A // p a}

/-- A uniform operation supplying the inverse of a bijection. -/
def BijectiveInverseSelector : Type (u + 1) :=
  ∀ (A B : Type u) (f : A → B), Function.Bijective f →
    {g : B → A // Function.LeftInverse g f ∧ Function.RightInverse g f}

/-- In a bijection each fiber has a unique element, so unique-witness
extraction is sufficient to construct its inverse. -/
def UniqueWitnessSelector.bijectiveInverses (select : UniqueWitnessSelector.{u}) :
    BijectiveInverseSelector.{u} :=
  fun A B f hf =>
    let fiber : ∀ b, {a : A // f a = b} := fun b =>
      select A (fun a => f a = b) (by
        obtain ⟨a, ha⟩ := hf.2 b
        exact ⟨a, ha, fun c hc => hf.1 (hc.trans ha.symm)⟩)
    ⟨fun b => (fiber b).val,
      fun a => hf.1 (fiber (f a)).property,
      fun b => (fiber b).property⟩

/-- A unique-witness subtype is in bijection with the singleton type.
An inverse construction for bijections therefore extracts its witness. -/
def BijectiveInverseSelector.uniqueWitnesses (inverses : BijectiveInverseSelector.{u}) :
    UniqueWitnessSelector.{u} :=
  fun A p unique =>
    let f : {a : A // p a} → PUnit.{u + 1} := fun _ => PUnit.unit
    let bijective : Function.Bijective f := by
      constructor
      · intro a b _
        apply Subtype.ext
        obtain ⟨x, _, hx⟩ := unique
        exact (hx a.val a.property).trans (hx b.val b.property).symm
      · intro b
        obtain ⟨a, ha, _⟩ := unique
        exact ⟨⟨a, ha⟩, by cases b; rfl⟩
    (inverses {a : A // p a} PUnit f bijective).val PUnit.unit

/-- Uniform inverse construction for bijections corresponds to unique
witness extraction; this equivalence does not assert arbitrary choice. -/
theorem uniqueWitnessSelector_iff_bijectiveInverses :
    Nonempty (UniqueWitnessSelector.{u}) ↔ Nonempty (BijectiveInverseSelector.{u}) := by
  constructor
  · intro h
    obtain ⟨select⟩ := h
    exact ⟨select.bijectiveInverses⟩
  · intro h
    obtain ⟨inverses⟩ := h
    exact ⟨inverses.uniqueWitnesses⟩

end Adiabatic.ChoiceReduction
